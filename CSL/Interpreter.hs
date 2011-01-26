{-# LANGUAGE FunctionalDependencies, FlexibleInstances, FlexibleContexts
  , UndecidableInstances, OverlappingInstances, MultiParamTypeClasses
  , TypeSynonymInstances, ExistentialQuantification #-}
{- |
Module      :  $Header$
Description :  Interpreter for CPL programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (various glasgow extensions)

Defines an interface for Calculators used to evaluate CPL programs
-}

module CSL.Interpreter
    ( AssignmentStore(..)
    , SMem(..)
    , isDefined
    , evaluate
    , evaluateList
    , loadAS
    , BMap(..)
    , BMapDefault(..)
    , fromList, defaultLookup, defaultRevlookup, CSL.Interpreter.empty, initWithDefault
    , lookupOrInsert
    , revlookup
    , rolookup
    , translateArgVars
    , translateExpr
    , translateExprWithVars
    , revtranslateExpr
    , revtranslateExprWithVars
    , stepwise
    , interactiveStepper
    , readEvalPrintLoop
    , EvalAtom(..)
    , prettyEvalAtom
    )
    where

import Control.Monad (liftM, forM_, filterM, unless)
import Control.Monad.State (StateT, MonadState (..))
import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List (mapAccumL)
import Prelude hiding (lookup)
import System.IO

import Common.Id
import Common.ResultT
import Common.Doc
import Common.DocUtils

import CSL.AS_BASIC_CSL

-- ----------------------------------------------------------------------
-- * Evaluator
-- ----------------------------------------------------------------------

-- ** some general lifted instances
-- TODO: outsource them

instance (MonadState s m, MonadTrans t, Monad (t m)) => MonadState s (t m) where
    get = lift get
    put = lift . put

instance (MonadIO m, MonadTrans t, Monad (t m)) => MonadIO (t m) where
    liftIO = lift . liftIO

instance (MonadResult m, MonadTrans t, Monad (t m)) => MonadResult (t m) where
    liftR = lift . liftR


-- ** Some utility classes for abstraction of concrete realizations

-- | Abstraction from lists, sets, etc. for some simple operations
class SimpleMember a b | a -> b where
    member :: b -> a -> Bool
    count :: a -> Int
    toList :: a -> [b]

-- ** Abstraction wrapper for utility classes
data SMem b = forall a. SimpleMember a b => SMem a

-- ** Instances for abstraction wrapper
instance SimpleMember (SMem b) b where
    member x (SMem a) = member x a
    count (SMem a) = count a
    toList (SMem a) = toList a


-- | Calculation interface, bundles the evaluation engine and the
-- assignment store
class (Monad m) => AssignmentStore m where
    assign :: ConstantName -> AssDefinition -> m EXPRESSION
    assigns :: [(ConstantName, AssDefinition)] -> m ()
    assigns = mapM_ $ uncurry assign
    lookup :: ConstantName -> m (Maybe EXPRESSION)
    names :: m (SMem ConstantName)
    eval :: EXPRESSION -> m EXPRESSION
    evalRaw :: String -> m String
    check :: EXPRESSION -> m Bool
    check = error "AssignmentStore-default: 'check' not implemented."
    values :: m [(ConstantName, EXPRESSION)]
    values = let f x = do
                   v <- lookup x
                   return (x, fromJust v)
             in names >>= mapM f . toList


instance AssignmentStore m => AssignmentStore (StateT s m) where
    assign s = lift . assign s
    lookup = lift . lookup
    names = lift names
    eval = lift . eval
    evalRaw = lift . evalRaw
    check = lift . check
    values = lift values

isDefined :: AssignmentStore m => ConstantName -> m Bool
isDefined s = liftM (member s) names

evaluate :: AssignmentStore m => CMD -> m ()
evaluate (Ass (Op (OpUser n) [] l _) e) = do
    assign n $ mkDefinition (toArgList l) e
    return ()
evaluate (Cond l) = do
  cl <- filterM (check . fst) l
  if null cl
    then error "evaluate: non-exhaustive conditional"
    else evaluateList $ snd $ head cl
evaluate (Repeat e l) =
    let f = do
          -- first run of the repeat loop
          evaluateList l
          b <- check e
          -- repeat f until condition holds
          unless b f
    in f
evaluate (Sequence l) = evaluateList l

evaluate (Cmd c _) = error $ "evaluate: unsupported command " ++ c
evaluate a@(Ass (Op (OpId _) _ _ _) _) =
    error $ concat [ "evaluate: predefined constants in left hand side of "
                   , "assignment not allowed ", show a ]
evaluate a@(Ass _ _) = error $ "evaluate: unsupported assignment " ++ show a


evaluateList :: AssignmentStore m => [CMD] -> m ()
evaluateList l = forM_ l evaluate


data EvalAtom = AssAtom ConstantName AssDefinition
              | RepeatAtom EXPRESSION | CaseAtom EXPRESSION deriving Show

prettyEvalAtom :: EvalAtom -> Doc
prettyEvalAtom (AssAtom c def) = pretty c <+> pretty def
prettyEvalAtom (RepeatAtom e) = text "Repeat condition:" <+> pretty e
prettyEvalAtom (CaseAtom e) = text "Case condition:" <+> pretty e

readEvalPrintLoop  :: (MonadIO m, AssignmentStore m) =>
                  Handle -- ^ Input handle
               -> Handle -- ^ Output handle
               -> String -- ^ Command prompt
               -> (String -> Bool) -- ^ Exit command predicate
               -> m ()
readEvalPrintLoop inp outp cp exitWhen = do
  s <- liftIO $ hPutStr outp cp >> hFlush outp >> hGetLine inp
  unless (exitWhen s) $ evalRaw s >>= liftIO . (hPutStrLn outp)
             >> readEvalPrintLoop inp outp cp exitWhen

interactiveStepper :: (MonadIO m, AssignmentStore m) => m () -> EvalAtom
                   -> m Bool
interactiveStepper prog x = do
  liftIO $ putStrLn $ "At step " ++ show (prettyEvalAtom x)
  b <- evaluateAtom prog x
  readEvalPrintLoop stdin stdout "next>" null
  return b

evaluateAtom :: AssignmentStore m => m () -> EvalAtom -> m Bool
evaluateAtom _ (AssAtom n def) = assign n def >> return True
evaluateAtom _ (CaseAtom e) = check e
evaluateAtom prog (RepeatAtom e) = prog >> check e

stepwise :: AssignmentStore m => (m () -> EvalAtom -> m Bool) -> CMD
         -> m ()
stepwise f (Ass (Op (OpUser n) [] l _) e) = do
  let def = mkDefinition (toArgList l) e
  f (return ()) $ AssAtom n def
  return ()
stepwise _ (Cond []) = error "stepwise: non-exhaustive conditional"
stepwise f (Cond ((e, pl):cl)) = do
  b <- f (return ()) $ CaseAtom e
  stepwise f $ if b then Sequence pl else Cond cl
stepwise f p@(Repeat e l) = do
  b <- f (stepwise f $ Sequence l) $ RepeatAtom e
  unless b $ stepwise f p
stepwise f (Sequence l) = mapM_ (stepwise f) l

stepwise _ (Cmd c _) = error $ "stepwise: unsupported command " ++ c
stepwise _ a@(Ass (Op (OpId _) _ _ _) _) =
    error $ concat [ "stepwise: predefined constants in left hand side of "
                   , "assignment not allowed ", show a ]
stepwise _ a@(Ass _ _) = error $ "stepwise: unsupported assignment " ++ show a


-- | Loads a dependency ordered assignment list into the store.
loadAS :: AssignmentStore m => [(ConstantName, AssDefinition)] -> m ()
loadAS = assigns . reverse

-- ----------------------------------------------------------------------
-- * Term translator
-- ----------------------------------------------------------------------

-- | A data structure for invertible maps, with automatic new key generation
-- and insertion at lookup
data BMap = BMap { mThere :: Map.Map ConstantName Int
                 , mBack :: IMap.IntMap ConstantName
                 , newkey :: Int
                 , prefix :: String
                 , defaultMap :: BMapDefault OPID
                 }
            deriving Show


data BMapDefault a = BMapDefault { mThr :: Map.Map a String
                                 , mBck :: Map.Map String a }

instance Show a => Show (BMapDefault a) where
    show _ = "BMapDefault"


instance SimpleMember BMap ConstantName where
    member k = Map.member k . mThere
    count = Map.size . mThere
    toList = Map.keys . mThere


-- ** Interface functions for BMapDefault

fromList :: Ord a => [(a, String)] -> BMapDefault a
fromList l = let f (x, y) = (y, x)
             in BMapDefault (Map.fromList l) $ Map.fromList $ map f l

defaultLookup :: Ord a => BMapDefault a -> a -> Maybe String
defaultLookup bmd s = Map.lookup s $ mThr bmd

defaultRevlookup :: BMapDefault a -> String -> Maybe a
defaultRevlookup bmd s = Map.lookup s $ mBck bmd

-- ** Interface functions for BMap
empty :: BMap
empty = BMap Map.empty IMap.empty 1 "x" $ fromList []

initWithDefault :: [(OPNAME, String)] -> BMap
initWithDefault l =
    let f (x, y) = (OpId x, y)
    in BMap Map.empty IMap.empty 1 "x" $ fromList $ map f l

-- | The only way to also insert a value is to use lookup. One should not
-- insert values explicitly. Note that you don't control the inserted value.
-- For (Left "...") we throw an error if this value is in the defaultMap,
-- for (Right (OpId ...)) we throw an error if it isn't.
lookupOrInsert :: BMap
               -> Either ConstantName OPID -- ^ If you provide a 'ConstantName'
                                           -- it is interpreted as an 'OpUser'
                                           -- value
               -> (BMap, String)
lookupOrInsert m k =
    let err pc = error $ "lookupOrInsert: predefined constant encountered "
                 ++ show pc
        (k', c, isL, isOpName) = case k of
                              Left s -> (OpUser s, s, True, False)
                              Right oi@(OpId _) -> (oi, err oi, False, True)
                              Right os@(OpUser x) -> (os, x, False, False)
    in
      case defaultLookup (defaultMap m) k' of
        Just s -> if isL
                  then error $ "lookupOrInsert: default functions should be "
                           ++ "passed in as OPIDs but got the constant "
                           ++ show c
                  else (m, s)
        Nothing
          | isOpName ->
              error $ "lookupOrInsert: OPNAMEs should be registered in the"
                        ++ " default mapping but could not find " ++ show k'
          | otherwise ->
              let f _ _ x = x
                  nv = newkey m
                  (mNv', nm) = Map.insertLookupWithKey f c nv $ mThere m
              -- first check for default symbols
              in case mNv' of
                   Just nv' -> (m, bmapIntToString m nv')
                   _ ->  (m { mThere = nm
                            , mBack = IMap.insert nv c $ mBack m
                            , newkey = nv + 1 }
                         , bmapIntToString m nv)

-- | A read-only version of 'lookupOrInsert'
rolookup :: BMap
         -> Either ConstantName OPID -- ^ If you provide a 'ConstantName'
                                     -- it is interpreted as an 'OpUser' value
         -> Maybe String
rolookup m k =
    let err pc = error $ "rolookup: predefined constant encountered "
                 ++ show pc
        (k', c, isL, isOpName) = case k of
                              Left s -> (OpUser s, s, True, False)
                              Right oi@(OpId _) -> (oi, err oi, False, True)
                              Right os@(OpUser x) -> (os, x, False, False)
    in
      case defaultLookup (defaultMap m) k' of
        Nothing
          | isOpName ->
              error $ "rolookup: OPNAMEs should be registered in the"
                        ++ " default mapping but could not find " ++ show k'
          | otherwise ->
              fmap (bmapIntToString m) $ Map.lookup c $ mThere m
        mS -> if isL
              then error $ "lookupOrInsert: default functions should be "
                       ++ "passed in as OPIDs but got the constant "
                       ++ show c
              else mS

revlookup :: BMap -> String -> (Maybe OPID)
revlookup m k = case revlookupGen IMap.empty m k of
                  Left x -> x
                  _ -> Nothing

revlookupGen :: RevVarMap -> BMap -> String
             -> Either (Maybe OPID) (Maybe EXPRESSION)
revlookupGen vm m k = 
    case defaultRevlookup (defaultMap m) k of
      Nothing ->
          case bmapStringToInt m k of
            Left i -> Left $ fmap OpUser $ IMap.lookup i $ mBack m
            Right i -> Right $ fmap (Var . mkSimpleId) $ IMap.lookup i $ vm
      mS -> Left mS


{-
bmToList :: BMap -> [(ConstantName, String)]
bmToList m = let prf = prefix m
                 f (x, y) = (x, prf ++ show y)
             in map f $ Map.toList $ mThere m
-}

-- ** Internal functions for BMap
bmapIntToString :: BMap -> Int -> String
bmapIntToString m i = prefix m ++ show i

-- | Returns the 'Int' contained in the given constant. If this constant
-- represents a user-defined constant then we return the left value, if
-- it represents a variable then we return the right value
bmapStringToInt :: BMap -> String -> Either Int Int
bmapStringToInt m s =
    let prf = prefix m
        (prf', n) = splitAt (length prf) s
        (prf'', n') = splitAt 1 s
        out
            | prf == prf' = Left $ read n
            | prf'' == "v" = Right $ read n'
            | otherwise = error $ concat [ "bmapStringToInt: invalid string"
                                         , " for prefix ", prf, ":", s ]
    in out


-- ** Translation functions for (generic) BMaps

type VarMap = Map.Map String Int
type RevVarMap = IMap.IntMap String

varList :: [String] -> [(String, Int)]
varList l = zip l [1..]

revVarList :: [String] -> [(Int, String)]
revVarList l = zip [1..] l 

varName :: BMap -> Int -> String
varName _ i = "v" ++ show i

translateArgVars :: BMap -> [String] -> [String]
translateArgVars m = map f . varList where
    f (_, i) = varName m i

translateExprWithVars :: [String] -> BMap -> EXPRESSION -> (BMap, EXPRESSION)
translateExprWithVars = translateExprGen . Map.fromList . varList

translateExpr :: BMap -> EXPRESSION -> (BMap, EXPRESSION)
translateExpr = translateExprGen Map.empty

-- | Translate EXPRESSION into a CAS compatible form. Variables are translated
-- as constants with a namespace disjoint from that of the usual constants.
translateExprGen :: VarMap -> BMap -> EXPRESSION -> (BMap, EXPRESSION)
translateExprGen vm m (Op oi epl el rg) =
    let (m', el') = mapAccumL (translateExprGen vm) m el
        (m'', s) = lookupOrInsert m' $ Right oi
    in (m'', Op (OpUser $ SimpleConstant s) epl el' rg)
translateExprGen vm m (List el rg) =
    let (m', el') = mapAccumL (translateExprGen vm) m el
    in (m', List el' rg)
translateExprGen vm m (Var tok) =
    let err = error $ "translateExprGen: Variable not mapped: " ++ show tok
        i = Map.findWithDefault err (tokStr tok) vm
    in (m, Op (OpUser $ SimpleConstant $ varName m i) [] [] nullRange)
translateExprGen _ m e = (m, e)

-- | Retranslate CAS EXPRESSION back, we do not allow OPNAMEs as OpIds

revtranslateExprWithVars :: [String] -> BMap -> EXPRESSION -> EXPRESSION
revtranslateExprWithVars = revtranslateExprGen . IMap.fromList . revVarList

revtranslateExpr :: BMap -> EXPRESSION -> EXPRESSION
revtranslateExpr = revtranslateExprGen IMap.empty

revtranslateExprGen :: RevVarMap -> BMap -> EXPRESSION -> EXPRESSION
revtranslateExprGen rvm m (Op (OpUser c) epl el rg) =
    case c of
      SimpleConstant s ->
          let el' = map (revtranslateExprGen rvm m) el
          in case revlookupGen rvm m s of
               Left (Just oi) -> Op oi epl el' rg
               Right (Just v) -> v
               _ -> error $ "revtranslateExpr: no mapping for " ++ s
      _ -> error $ "revtranslateExpr: elim constants on CAS side not"
           ++  " supported " ++ show c
revtranslateExprGen rvm m (List el rg) =
    let el' = map (revtranslateExprGen rvm m) el
    in List el' rg
revtranslateExprGen _ _ e = e


-- ** Pretty printing of BMap
-- (Pretty a, Pretty b) => 

-- pm = ppMap pa text braces vcat printMapping

printMapping :: Doc -> Doc -> Doc
printMapping x y = x <+> mapsto <+> y

printBMapDefault :: (a -> Doc) -> BMapDefault a -> Doc
printBMapDefault pa bm =
    ppMap pa text box vcat printMapping $ mThr bm where
        box = (text "BMapDefault" $+$) . braces

printBMap :: BMap -> Doc
printBMap bm =
    braces $ text "BMap" $+$ md $++$ mdefault
        where
          md = printMap braces vcat printMapping $ mThere bm
          mdefault = printBMapDefault pretty $ defaultMap bm

instance Pretty a => Pretty (BMapDefault a) where
    pretty = printBMapDefault pretty

instance Pretty BMap where
    pretty = printBMap



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
    , fromList, defaultLookup, defaultRevlookup, CSL.Interpreter.empty
    , initWithDefault
    , genKey
    , lookupOrInsert
    , revlookup
    , rolookup
    , translateArgVars
    , translateExpr
    , translateExprWithVars
    , revtranslateExpr
    , revtranslateExprWithVars
    , stepwise
    , stepwiseSafe
    , interactiveStepper
    , readEvalPrintLoop
    , EvalAtom(..)
    , prettyEvalAtom
    , asErrorMsg
    , ASError(..)
    )
    where

import Control.Monad (liftM, forM_, filterM, unless)
import Control.Monad.State (StateT, MonadState (..))
import Control.Monad.Error (Error(..), MonadError (..))
import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List (mapAccumL)
import Prelude hiding (lookup)
import System.IO

import Common.Id
import Common.ResultT
import Common.Doc
import Common.DocUtils
import Common.Utils

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
    getUndefinedConstants :: EXPRESSION -> m (Set.Set ConstantName)
    getUndefinedConstants = error ""
    genNewKey :: m Int
    genNewKey = error ""


instance AssignmentStore m => AssignmentStore (StateT s m) where
    assign s = lift . assign s
    assigns = lift . assigns
    lookup = lift . lookup
    names = lift names
    eval = lift . eval
    evalRaw = lift . evalRaw
    check = lift . check
    values = lift values
    getUndefinedConstants = lift . getUndefinedConstants
    genNewKey = lift genNewKey

data ASError = CASError String | UserError String deriving Show

asErrorMsg :: ASError -> String
asErrorMsg (CASError s) = s
asErrorMsg (UserError s) = s

instance Error ASError where
    noMsg = UserError ""
    strMsg = UserError

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

instance Pretty EvalAtom where
    pretty = prettyEvalAtom

readEvalPrintLoop  :: (MonadIO m, AssignmentStore m) =>
                  Handle -- ^ Input handle
               -> Handle -- ^ Output handle
               -> String -- ^ Command prompt
               -> (String -> Bool) -- ^ Exit command predicate
               -> m String
readEvalPrintLoop inp outp cp exitWhen = do
  s <- liftIO $ hPutStr outp cp >> hFlush outp >> hGetLine inp
  if exitWhen s then return s
   else evalRaw s >>= liftIO . (hPutStrLn outp)
            >> readEvalPrintLoop inp outp cp exitWhen

-- | An atom evaluator for 'stepwise' which pauses at each atomic evaluation
-- position.
interactiveStepper :: (MonadIO m, AssignmentStore m) => m () -> EvalAtom
                   -> m Bool
interactiveStepper prog x = do
  liftIO $ putStrLn $ "At step " ++ show (prettyEvalAtom x)
  b <- evaluateAtom prog x
  readEvalPrintLoop stdin stdout "next>" null
  return b

-- | The most primitive atom evaluator as expected by 'stepwise'.
evaluateAtom :: AssignmentStore m => m () -> EvalAtom -> m Bool
evaluateAtom _ (AssAtom n def) = assign n def >> return True
evaluateAtom _ (CaseAtom e) = check e
evaluateAtom prog (RepeatAtom e) = prog >> check e

{- | It is assumed that the given function respects the evaluation semantics,
   i.e., that for the assignment atom an assignment takes place and for the
   repeat atom the passed program is evaluated and afterwards the condition is
   checked and for the case atom the condition is checked. See 'evaluateAtom'
   for an example.
-}
stepwiseSafe :: (MonadError ASError m, AssignmentStore m) =>
                (m () -> EvalAtom -> m Bool) -> CMD -> m (Maybe ASError)
stepwiseSafe f cmd = catchError (stepwise f cmd >> return Nothing) g
    where g = return . Just
      



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
stepwise f (Repeat e l) = do
  -- only in the first entry of a repeat loop we need to transform the
  -- until expression, in all consecutive runs of the same loop we just
  -- need to update the values of the temporarily introduced constants.
  (m, e') <- translateConvergence e
  let al = Map.toList m
      -- we check if the expression contains free constants
      -- (undefined in the assignment graph) and in this case we replace the
      -- definition of the constant by the undefined constant.
      g (conve, i) = do
        s <- getUndefinedConstants conve
        let e'' = if Set.null s then conve else mkPredefOp OP_undef []
        return (internalConstant i, mkDefinition [] e'')
      reploop = do
        mapM g al >>= assigns
        b <- f (stepwise f $ Sequence l) $ RepeatAtom e'
        unless b $ reploop
  reploop
stepwise f (Sequence l) = mapM_ (stepwise f) l

stepwise _ (Cmd c _) = error $ "stepwise: unsupported command " ++ c
stepwise _ a@(Ass (Op (OpId _) _ _ _) _) =
    error $ concat [ "stepwise: predefined constants in left hand side of "
                   , "assignment not allowed ", show a ]
stepwise _ a@(Ass _ _) = error $ "stepwise: unsupported assignment " ++ show a

translateConvergence :: AssignmentStore m =>
                        EXPRESSION -> m (Map.Map EXPRESSION Int, EXPRESSION)
translateConvergence e' = f Map.empty e' where
    f m (Op (OpId OP_convergence) [] [e, x] rg) =
        do
          i <- genNewKey
          let ilf _ _ v = v
              (mI, m') = Map.insertLookupWithKey ilf e i m
              i' = fromMaybe i mI
              genC = Op (OpUser $ internalConstant i') [] [] rg
          return (m', mkPredefOp OP_reldistLe [genC, e, x])
    f m (Op oi epl el rg) =
        liftM (\ (m', x) -> (m', Op oi epl x rg)) $ mapAccumLM f m el
    -- ignoring lists, see TODO in AS_BASIC_CSL
    f m e = return (m, e)
    

-- | Loads a dependency ordered assignment list into the store.
loadAS :: AssignmentStore m => [(ConstantName, AssDefinition)] -> m ()
loadAS = assigns . reverse

-- ----------------------------------------------------------------------
-- * Term translator
-- ----------------------------------------------------------------------

{- | For use for constants in the CAS namespace.
   We only need to make sure that x<Num> is not already used in the
   default namespace of the CAS in question. We take for all CAS the
   same prefix, namely "x".
-}
constPrefix :: String
constPrefix = "x"
{- | The variable prefix is used for auxiliary variables in the CAS namespace.
   We use the prefix "v". The same remarks are valid as for 'constPrefix'.
-}
varPrefix :: String
varPrefix = "v"

{- | For use for auxiliary constants in the EnCL specification
   namespace. A dollar prefix is suitable here because this prefix is not
   accepted by the input processor for user defined constants.
-}
internalPrefix :: String
internalPrefix = "$"

internalConstant :: Int -> ConstantName
internalConstant i = SimpleConstant $ internalPrefix ++ show i

-- | The undefined constant in the CAS namespace.
undefConstant :: String
undefConstant = show OP_undef

-- | A data structure for invertible maps, with automatic new key generation
-- and insertion at lookup
data BMap = BMap { mThere :: Map.Map ConstantName Int
                 , mBack :: IMap.IntMap ConstantName
                 , newkey :: Int
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


genKey :: BMap -> (BMap, Int)
genKey bm = let i = newkey bm in (bm { newkey = i+1 }, i) 

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
empty = BMap
        { mThere =  Map.empty
        , mBack = IMap.empty
        , newkey =  1
        , defaultMap = fromList []
        }

initWithDefault :: [(OPNAME, String)] -> BMap
initWithDefault l =
    let f (x, y) = (OpId x, y)
        -- this mapping should be always there, but may be overwritten
        l' = (OP_undef, undefConstant):l
    in CSL.Interpreter.empty {defaultMap = fromList $ map f l'}

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
              then error $ "rolookup: default functions should be "
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
bmToList m = let prf = constPrefix
                 f (x, y) = (x, prf ++ show y)
             in map f $ Map.toList $ mThere m
-}

-- ** Internal functions for BMap
bmapIntToString :: BMap -> Int -> String
bmapIntToString _ i = constPrefix ++ show i

-- | Returns the 'Int' contained in the given constant. If this constant
-- represents a user-defined constant then we return the left value, if
-- it represents a variable then we return the right value
bmapStringToInt :: BMap -> String -> Either Int Int
bmapStringToInt _ s =
    let prf = constPrefix
        (prf', n) = splitAt (length prf) s
        (prf'', n') = splitAt 1 s
        out
            | prf == prf' = Left $ read n
            | prf'' == varPrefix = Right $ read n'
            | otherwise = error $ concat [ "bmapStringToInt: invalid string"
                                         , " for prefix ", prf, ":", s ]
    in out


-- ** Translation functions for (generic) BMaps

type VarMap = Map.Map String Int
type RevVarMap = IMap.IntMap String

varList :: [String] -> [(String, Int)]
varList l = zip l [1..]

addToVarMap :: VarMap -> String -> VarMap
addToVarMap vm s = Map.insert s (Map.size vm + 1) vm 

revVarList :: [String] -> [(Int, String)]
revVarList l = zip [1..] l 

varName :: BMap -> Int -> String
varName _ i = varPrefix ++ show i

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
    let (m', s) = lookupOrInsert m $ Right oi
        vm' = case lookupBindInfo oi $ length el of
                Just bi -> 
                    foldl addToVarMap vm
                              $ toArgList $ map (el!!) $ bindingVarPos bi
                _ -> vm
        (m'', el') = mapAccumL (translateExprGen vm') m' el
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

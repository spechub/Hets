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

module CSL.Interpreter where

import Control.Monad (liftM, forM_, filterM, unless)
import Control.Monad.State (StateT, MonadState (..))
import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List (mapAccumL)
import Prelude hiding (lookup)

import Common.ResultT

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

-- | calculation interface, bundles the evaluation engine and the constant store
class (Monad m) => AssignmentStore m where
    assign :: ConstantName -> EXPRESSION -> m ()
    lookup :: ConstantName -> m (Maybe EXPRESSION)
    names :: m (SMem ConstantName)
    eval :: EXPRESSION -> m EXPRESSION
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
    check = lift . check
    values = lift values

isDefined :: AssignmentStore m => ConstantName -> m Bool
isDefined s = liftM (member s) names

evaluate :: AssignmentStore m => CMD -> m ()
evaluate (Ass (Op (OpUser n) [] [] _) e) = assign n e
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
    error $ "evaluate: OPNAME in left hand side of assignment not allowed "
              ++ show a
evaluate a@(Ass _ _) = error $ "evaluate: unsupported assignment " ++ show a


evaluateList :: AssignmentStore m => [CMD] -> m ()
evaluateList l = forM_ l evaluate

-- ----------------------------------------------------------------------
-- * Term translator
-- ----------------------------------------------------------------------

-- | A data structure for invertible maps, with automatic new key generation
-- and insertion at lookup
data BMap = BMap { mThere :: Map.Map ConstantName Int
                 , mBack :: IMap.IntMap ConstantName
                 , newkey :: Int
                 , prefix :: String
                 , defaultMap :: BMapDefault OPID }


data BMapDefault a = BMapDefault { mThr :: Map.Map a String
                                 , mBck :: Map.Map String a }


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
                                           -- it is interpreted as an OpUser
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
                     ++ "passed in as OPIDs but got the constant " ++ show c
                else (m, s)
      _ -> let f _ _ x = x
               nv = newkey m
               (mNv', nm) = Map.insertLookupWithKey f c nv $ mThere m
           -- first check for default symbols
           in if isOpName
              then error $ "lookupOrInsert: OPNAMEs should be registered in the"
                       ++ " default mapping but could not find " ++ show k'
              else case mNv' of
                Just nv' -> (m, bmapIntToString m nv')
                _ ->  (m { mThere = nm
                         , mBack = IMap.insert nv c $ mBack m
                         , newkey = nv + 1 }
                      , bmapIntToString m nv)

revlookup :: BMap -> String -> OPID
revlookup m k = 
    case defaultRevlookup (defaultMap m) k of
      Just s -> s
      _ -> let i = bmapStringToInt m k
               err = error $ "revlookup: No reverse mapping for " ++ k
           in OpUser $ IMap.findWithDefault err i $ mBack m

bmToList :: BMap -> [(ConstantName, String)]
bmToList m = let prf = prefix m
                 f (x, y) = (x, prf ++ show y)
             in map f $ Map.toList $ mThere m

-- ** Internal functions for BMap
bmapIntToString :: BMap -> Int -> String
bmapIntToString m i = prefix m ++ show i

bmapStringToInt :: BMap -> String -> Int
bmapStringToInt m s = let prf = prefix m
                          (prf', n) = splitAt (length prf) s
                      in if prf == prf' then read n
                         else error $ concat [ "bmapStringToInt: invalid string"
                                             , " for prefix ", prf, ":", s ]


-- ** Translation functions for (generic) BMaps

-- | Translate EXPRESSION into a CAS compatible form
translateEXPRESSION :: BMap -> EXPRESSION -> (BMap, EXPRESSION)
translateEXPRESSION m (Op oi epl el rg) =
    let (m', el') = mapAccumL translateEXPRESSION m el
        (m'', s) = lookupOrInsert m' $ Right oi
    in (m'', Op (OpUser $ SimpleConstant s) epl el' rg)
translateEXPRESSION m (List el rg) =
    let (m', el') = mapAccumL translateEXPRESSION m el
    in (m', List el' rg)
translateEXPRESSION m e = (m, e)

-- | Retranslate CAS EXPRESSION back, we do not allow OPNAMEs as OpIds
revtranslateEXPRESSION :: BMap -> EXPRESSION -> EXPRESSION
revtranslateEXPRESSION m (Op (OpUser c) epl el rg) =
    case c of
      SimpleConstant s ->
          let el' = map (revtranslateEXPRESSION m) el
              oi = revlookup m s
          in Op oi epl el' rg
      _ -> error $ "revtranslateEXPRESSION: elim constants on CAS side not"
           ++  " supported " ++ show c
revtranslateEXPRESSION m (List el rg) =
    let el' = map (revtranslateEXPRESSION m) el
    in List el' rg
revtranslateEXPRESSION _ e = e

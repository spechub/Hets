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
import Control.Monad.State (State, MonadState (..))
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

-- ** some general lifted instances, TODO: outsource them

instance (MonadState s m, MonadTrans t, Monad (t m)) => MonadState s (t m) where
    get = lift get
    put = lift . put

instance (MonadIO m, MonadTrans t, Monad (t m)) => MonadIO (t m) where
    liftIO = lift . liftIO

instance (MonadResult m, MonadTrans t, Monad (t m)) => MonadResult (t m) where
    liftR = lift . liftR


-- | Abstraction from lists, sets, etc. for some simple operations
class SimpleMember a b | a -> b where
    member :: b -> a -> Bool
    count :: a -> Int
    toList :: a -> [b]

data SMem b = forall a. SimpleMember a b => SMem a

instance SimpleMember (SMem b) b where
    member x (SMem a) = member x a
    count (SMem a) = count a
    toList (SMem a) = toList a

instance Ord a => SimpleMember (Map.Map a b) a where
    member = Map.member
    count = Map.size
    toList = Map.keys

-- | calculation interface, bundles the evaluation engine and the constant store
class (Monad m) => CalculationSystem m where
    assign :: String -> EXPRESSION -> m () -- evtl. m Bool instead as success-flag
    clookup :: String -> m (Maybe EXPRESSION)
    names :: m (SMem String)
    eval :: EXPRESSION -> m EXPRESSION
    check :: EXPRESSION -> m Bool
    check = error "CalculationSystem-default: 'check' not implemented."
    values :: m [(String, EXPRESSION)]
    values = let f x = do
                   v <- clookup x
                   return (x, fromJust v)
             in names >>= mapM f . toList


-- | Just an example which does not much, for illustration purposes
instance CalculationSystem (State (Map.Map String EXPRESSION))  where
    assign n e = liftM (Map.insert n e) get >> return ()
    clookup n = liftM (Map.lookup n) get
    names = error "" -- get
    eval e = return e
    check _ = return False

evaluate :: CalculationSystem m => CMD -> m ()
evaluate (Cmd ":=" [Op n [] [] _, e]) = assign n e
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
evaluate (Cmd c _) = error $ "evaluate: unsupported command " ++ c


evaluateList :: CalculationSystem m => [CMD] -> m ()
evaluateList l = forM_ l evaluate

-- ----------------------------------------------------------------------
-- * Term translator
-- ----------------------------------------------------------------------
{-
class InvMap m a b where
    lookup :: m -> a -> b
    revlookup :: m -> b -> a
-}

-- | A data structure for invertible maps, with automatic new key generation
-- and insertion at lookup
data BMap = BMap { mThere :: Map.Map String Int
                 , mBack :: IMap.IntMap String
                 , newkey :: Int
                 , prefix :: String
                 , defaultMap :: BMapDefault }


data BMapDefault = BMapDefault { mThr :: Map.Map String String
                               , mBck :: Map.Map String String }


instance SimpleMember BMap String where
    member k = Map.member k . mThere
    count = Map.size . mThere
    toList = Map.keys . mThere



-- ** Interface functions for BMapDefault

fromList :: [(String, String)] -> BMapDefault
fromList l = let f (x, y) = (y, x)
             in BMapDefault (Map.fromList l) $ Map.fromList $ map f l

defaultLookup :: BMapDefault -> String -> Maybe String
defaultLookup bmd s = Map.lookup s $ mThr bmd

defaultRevlookup :: BMapDefault -> String -> Maybe String
defaultRevlookup bmd s = Map.lookup s $ mBck bmd

-- ** Interface functions for BMap
empty :: BMap
empty = BMap Map.empty IMap.empty 1 "x" $ fromList []

initWithDefault :: [(String, String)] -> BMap
initWithDefault l = BMap Map.empty IMap.empty 1 "x" $ fromList l

-- | The only way to also insert a value is to use lookup. One should not
-- insert values explicitly. Note that you don't control the inserted value.
lookup :: BMap -> String -> (BMap, String)
lookup m k = 
    case defaultLookup (defaultMap m) k of
      Just s -> (m, s)
      _ -> let f _ _ x = x
               nv = newkey m
               (mNv', nm) = Map.insertLookupWithKey f k nv $ mThere m
           -- first check for default symbols
           in case mNv' of
                Just nv' -> (m, bmapIntToString m nv')
                _ ->  (m { mThere = nm
                         , mBack = IMap.insert nv k $ mBack m
                         , newkey = nv + 1 }
                      , bmapIntToString m nv)

revlookup :: BMap -> String -> String
revlookup m k = 
    case defaultRevlookup (defaultMap m) k of
      Just s -> s
      _ -> let i = bmapStringToInt m k
               err = error $ "revlookup: No reverse mapping for " ++ k
           in IMap.findWithDefault err i $ mBack m

bmToList :: BMap -> [(String, String)]
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
translateEXPRESSION m (Op s epl el rg) =
    let (m', el') = mapAccumL translateEXPRESSION m el
        (m'', s') = lookup m' s
    in (m'', Op s' epl el' rg)
translateEXPRESSION m (List el rg) =
    let (m', el') = mapAccumL translateEXPRESSION m el
    in (m', List el' rg)
translateEXPRESSION m e = (m, e)

-- | Retranslate CAS EXPRESSION back
revtranslateEXPRESSION :: BMap -> EXPRESSION -> EXPRESSION
revtranslateEXPRESSION m (Op s epl el rg) =
    let el' = map (revtranslateEXPRESSION m) el
        s' = revlookup m s
    in Op s' epl el' rg
revtranslateEXPRESSION m (List el rg) =
    let el' = map (revtranslateEXPRESSION m) el
    in List el' rg
revtranslateEXPRESSION _ e = e

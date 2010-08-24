{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Interpreter for CPL programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Defines an interface for Calculators used to evaluate CPL programs
-}

module CSL.Interpreter where

import Control.Monad (liftM, forM_, filterM, unless)
import Control.Monad.State (State, MonadState (..))
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List (mapAccumL)
import Prelude hiding (lookup)


import CSL.AS_BASIC_CSL

-- ----------------------------------------------------------------------
-- * Evaluator
-- ----------------------------------------------------------------------

-- | calculation interface, bundles the evaluation engine and the constant store
class Monad m => CalculationSystem m where
    assign :: String -> EXPRESSION -> m () -- evtl. m Bool instead as success-flag
    clookup :: String -> m (Maybe EXPRESSION)
    names :: m [String]
    eval :: EXPRESSION -> m EXPRESSION
    check :: EXPRESSION -> m Bool
    check = error "CalculationSystem-default: 'check' not implemented."
    values :: m [(String, EXPRESSION)]
    values = let f x = do
                   v <- clookup x
                   return (x, fromJust v)
             in names >>= mapM f

-- | Just an example which does not much, for illustration purposes
instance CalculationSystem (State (Map.Map String EXPRESSION)) where
    assign n e = liftM (Map.insert n e) get >> return ()
    clookup n = liftM (Map.lookup n) get
    names = liftM Map.keys get
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
                 , prefix :: String }

-- ** Interface functions for BMap
empty :: BMap
empty = BMap Map.empty IMap.empty 1 "x"

lookup :: BMap -> String -> (BMap, String)
lookup m k =  let f _ _ x = x
                  nv = newkey m
                  (mNv', nm) = Map.insertLookupWithKey f k nv $ mThere m
              in case mNv' of
                   Just nv' -> (m, bmapIntToString m nv')
                   Nothing ->  (m { mThere = nm
                                  , mBack = IMap.insert nv k $ mBack m
                                  , newkey = nv + 1 }
                               , bmapIntToString m nv)

revlookup :: BMap -> String -> String
revlookup m s = let i = bmapStringToInt m s
                    err = error $ "revlookup: No reverse mapping for " ++ s
                in IMap.findWithDefault err i $ mBack m
                    
toList :: BMap -> [(String, String)]
toList m = let prf = prefix m
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

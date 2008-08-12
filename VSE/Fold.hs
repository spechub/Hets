{- |
Module      :  $Header$
Description :  folding functions for VSE progams
Copyright   :  (c) Christian Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

folding functions for VSE progams
-}

module VSE.Fold where

import qualified Data.Set as Set
import CASL.AS_Basic_CASL
import VSE.As

-- | fold record
data FoldRec a = FoldRec
  { foldAbort :: Program -> a
  , foldSkip :: Program -> a
  , foldAssign :: Program -> VAR  -> TERM () -> a
  , foldCall :: Program ->  FORMULA () -> a
  , foldReturn :: Program -> (TERM ()) -> a
  , foldBlock :: Program -> [VAR_DECL] -> a -> a
  , foldSeq :: Program -> a -> a -> a
  , foldIf :: Program -> FORMULA () -> a -> a -> a
  , foldWhile :: Program -> FORMULA () -> a -> a }

-- | fold function
foldProg :: FoldRec a -> Program -> a
foldProg r p = case unRanged p of
  Abort -> foldAbort r p
  Skip -> foldSkip r p
  Assign v t-> foldAssign r p v t
  Call f -> foldCall r p f
  Return t -> foldReturn r p t
  Block vs q -> foldBlock r p vs $ foldProg r q
  Seq p1 p2 -> foldSeq r p (foldProg r p1) $ foldProg r p2
  If f p1 p2 -> foldIf r p f (foldProg r p1) $ foldProg r p2
  While f q -> foldWhile r p f $ foldProg r q

mapRec :: FoldRec Program
mapRec = FoldRec
  { foldAbort = id
  , foldSkip = id
  , foldAssign = \ (Ranged _ r) v t -> Ranged (Assign v t) r
  , foldCall = \ (Ranged _ r) f -> Ranged (Call f) r
  , foldReturn = \ (Ranged _ r) t -> Ranged (Return t) r
  , foldBlock = \ (Ranged _ r) vs p -> Ranged (Block vs p) r
  , foldSeq = \ (Ranged _ r) p1 p2 -> Ranged (Seq p1 p2) r
  , foldIf = \ (Ranged _ r) c p1 p2 -> Ranged (If c p1 p2) r
  , foldWhile = \ (Ranged _ r) c p -> Ranged (While c p) r }

mapProg :: (TERM () -> TERM ()) -> (FORMULA () -> FORMULA ())
        -> FoldRec Program
mapProg mt mf = mapRec
  { foldAssign = \ (Ranged _ r) v t -> Ranged (Assign v $ mt t) r
  , foldCall = \ (Ranged _ r) f -> Ranged (Call $ mf f) r
  , foldReturn = \ (Ranged _ r) t -> Ranged (Return $ mt t) r
  , foldIf = \ (Ranged _ r) c p1 p2 -> Ranged (If (mf c) p1 p2) r
  , foldWhile = \ (Ranged _ r) c p -> Ranged (While (mf c) p) r }

-- | collect i.e. variables to be universally bound on the top level
constProg :: (TERM () -> a) -> (FORMULA () -> a) -> ([a] -> a) -> a -> FoldRec a
constProg ft ff join c = FoldRec
  { foldAbort = const c
  , foldSkip = const c
  , foldAssign = \ _ _ t -> ft t
  , foldCall = \ _ f -> ff f
  , foldReturn = \ _ t -> ft t
  , foldBlock = \ _ _ p -> p
  , foldSeq = \ _ p1 p2 -> join [p1, p2]
  , foldIf = \ _ f p1 p2 -> join [ff f, p1, p2]
  , foldWhile = \ _ f p -> join [ff f, p] }

progToSetRec :: Ord a => (TERM () -> Set.Set a) -> (FORMULA () -> Set.Set a)
             -> FoldRec (Set.Set a)
progToSetRec ft ff = constProg ft ff Set.unions Set.empty
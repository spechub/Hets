{-# LANGUAGE DeriveGeneric #-}
{- |
Module      :  ./CspCASL/LocalTop.hs
Description :  Local top element analysis for CspCASL specifications
Copyright   :  (c) Andy Gimblett, Swansea University 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Analysis of relations for presence of local top elements.  Used by
CspCASL static analysis.

-}

module CspCASL.LocalTop (
    checkLocalTops,
    cartesian
) where

import CASL.AS_Basic_CASL (SORT)
import qualified Common.Lib.Rel as Rel
import Common.Result (Diagnosis (..), mkDiag, DiagKind (..))
import qualified Data.HashSet as S
import Data.Maybe
import GHC.Generics (Generic)
import Data.Hashable
-- | A relation is a set of pairs.
type Relation a b = S.HashSet (a, b)
type BinaryRelation a = Relation a a

{- | We're interested in triples where two elements are both in relation
with some third object.  We represent this as a Obligation, where
the first element is the shared one.  It's important to note that
(Obligation x y z) == (Obligation x z y), which we encode here.  For
every obligation, we look for any corresponding top elements. -}
data Obligation a = Obligation a a a
      deriving Generic

instance (Hashable a) => Hashable (Obligation a)

instance Eq a => Eq (Obligation a) where
    (Obligation n m o) == (Obligation x y z) =
        (n == x) && ((m, o) == (y, z) || (m, o) == (z, y))
instance Ord a => Ord (Obligation a) where
    compare (Obligation n m o) (Obligation x y z)
        | Obligation n m o == Obligation x y z = EQ
        | otherwise = compare (n, m, o) (x, y, z)
instance Show a => Show (Obligation a) where
    show (Obligation x y z) = show [x, y, z]

{- | Turn a binary relation into a set mapping its obligation elements to
their corresponding local top elements (if any). -}
localTops :: (Ord a, Hashable a) => BinaryRelation a -> S.HashSet (Obligation a, S.HashSet a)
localTops r = S.map (\ x -> (x, m x)) (obligations r)
    where m = findTops $ cartesian r

{- | Find all the obligations in a binary relation, by searching its
cartesian product for elements of the right form. -}
obligations :: (Ord a, Hashable a) => BinaryRelation a -> S.HashSet (Obligation a)
obligations r = stripMaybe $ S.map isObligation (cartesian r)
    where isObligation ((w, x), (y, z)) =
              if (w == y) && (x /= z) && (w /= z) && (w /= x)
              then Just (Obligation w x z)
              else Nothing

{- | Given a binary relation's cartesian product and a obligation, look
for corresponding top elements in that product. -}
findTops :: (Ord a, Hashable a)=> BinaryRelation (a, a) -> Obligation a -> S.HashSet a
findTops c cand = S.map get_top (S.filter (is_top cand) c)
    where is_top (Obligation _ y z) ((m, n), (o, p)) = (m == y && o == z) && (n == p)
          get_top ((_, _), (_, p)) = p


-- Utility functions.

-- | Cartesian product of a set.
cartesian :: (Ord a, Hashable a) => S.HashSet a -> S.HashSet (a, a)
cartesian x = S.fromList [(i, j) | i <- xs, j <- xs]
    where xs = S.toList x
    -- fromDistinctAscList sorted precondition satisfied by construction

-- | Given a set of Maybes, filter to keep only the Justs
stripMaybe :: (Ord a, Hashable a) => S.HashSet (Maybe a) -> S.HashSet a
stripMaybe x = S.fromList $ catMaybes $ S.toList x

-- | Given a binary relation, compute its reflexive closure.
reflexiveClosure :: (Ord a, Hashable a) => BinaryRelation a -> BinaryRelation a
reflexiveClosure r = S.foldr add_refl r r
    where add_refl (x, y) r' = (x, x) `S.insert` ((y, y) `S.insert` r')


{- | Main function for CspCASL LTE checks: given a
transitively-closed subsort relation as a list of pairs, return a
list of unfulfilled LTE obligations. -}
unmetObs :: (Ord a, Hashable a)=> [(a, a)] -> [Obligation a]
unmetObs r = unmets
    where l = S.toList $ localTops $ reflexiveClosure $ S.fromList r
          unmets = map fst $ filter (S.null . snd) l

{- Wrapper functions follow that allow easy calling for various situations
(static analysis and signature union). -}

{- | Add diagnostic error message for every unmet local top element
obligation. -}
lteError :: Obligation SORT -> Diagnosis
lteError (Obligation x y z) = mkDiag Error msg ()
    where msg = "local top element obligation ("
                ++ show x ++ " < " ++ show y ++ ", " ++ show z
                ++ ") unfulfilled"

{- | This is the main interface for the LTE check. Check a CspCASL signature
(actually just the sort relation) for local top elements in its subsort
relation. Returns empty list for sucess or a list of diags for failure where
diags is a list of diagnostic errors resulting from the check. -}
checkLocalTops :: Rel.Rel SORT -> [Diagnosis]
checkLocalTops sr =
    let obs = unmetObs (Rel.toList (Rel.transClosure sr))
    in map lteError obs

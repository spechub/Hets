{- |
Module      :  $Header$
Description :  Handling of extended parameter relations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines an ordering on extended parameters and other analysis tools.

Extended parameter relations have the property
 -}

module CSL.EPRelation
 ( EP.compareEP, EP.EPExp, EP.toEPExp, compareEPs, EPExps
 , toEPExps, forestFromEPs, makeEPLeaf, showEPForest
 , smtVMFromVars, smtExps, smtRange, smtPredDef, smtVarDef, smtVars, smtGenericStmt, smtEQStmt, smtLEStmt, smtDisjStmt
 )
    where

import qualified Data.Map as Map
import Data.Maybe
import Data.Tree
import Data.List (intercalate)
import Data.Traversable (fmapDefault)

import CSL.EPBasic
import CSL.TreePO
import CSL.AS_BASIC_CSL
---import CSL.GeneralExtendedParameter as EP
import CSL.ExtendedParameter as EP
    (toBoolRep, showEP, toEPExp, EPExp, compareEP)

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

-- | A more efficient representation of a list of extended parameters, 
-- particularly for comparison
type EPExps = Map.Map String EPExp

showEPs :: EPExps -> String
showEPs eps =
    let outp = intercalate ","
               $ map showEP $ Map.toList eps
    in if null outp then "*" else outp


-- | Conversion function into the more efficient representation.
toEPExps :: [EXTPARAM] -> EPExps
toEPExps = Map.fromList . mapMaybe toEPExp



data EPRange = Union EPRange EPRange | Intersection EPRange EPRange
             | Difference EPRange EPRange | Atom EPExps

-- ----------------------------------------------------------------------
-- * SMT output generation
-- ----------------------------------------------------------------------

type VarMap = Map.Map String Int

smtVMFromVars :: [String] -> VarMap
smtVMFromVars l = Map.fromList $ zip l $ [1 .. length l]

smtExps :: VarMap -> EPExps -> BoolRep
smtExps m eps = And $ map f $ Map.assocs eps where
    err = error "smtExps: No matching"
    f (k, v) = toBoolRep ("x" ++ show (Map.findWithDefault err k m)) v

smtRange :: VarMap -> EPRange -> BoolRep
smtRange m (Union a b) = Or [smtRange m a, smtRange m b]
smtRange m (Intersection a b) = And [smtRange m a, smtRange m b]
smtRange m (Difference a b) = And [smtRange m a, Not $ smtRange m b]
smtRange m (Atom eps) = smtExps m eps

smtPredDef :: VarMap -> String -> BoolRep -> String
smtPredDef m s b = "(define B::(-> int int bool) (lambda (x::int y::int) (and (<= 2 x) (<= x 5) (<= 1 y) (<= y 10))))"

smtVarDef :: VarMap -> String
smtVarDef m =
    unlines $ map (\ x -> "(define " ++ x ++ " ::int)") $ smtVars m "y"

smtVars :: VarMap -> String -> [String]
smtVars m s = map ((s++) . show) [1 .. Map.size m]

smtGenericStmt :: VarMap -> String -> String -> String -> String
smtGenericStmt m s a b =
    let vl = concat $ map (" "++) $ smtVars m "y"
    in "(assert (not (" ++ s ++ " (" ++ a ++ vl ++ ") (" ++ b ++ vl ++ "))))"

smtEQStmt :: VarMap -> String -> String -> String
smtEQStmt m a b = smtGenericStmt m "=" a b

smtLEStmt :: VarMap -> String -> String -> String
smtLEStmt m a b = smtGenericStmt m "=>" a b

smtDisjStmt :: VarMap -> String -> String -> String
smtDisjStmt m a b = smtGenericStmt m "and" a b


-- ----------------------------------------------------------------------
-- * Trees to store Extended Parameter indexed values
-- ----------------------------------------------------------------------

{- | We use trees with special labels of this type.


     In two assignments of the same constant we don't allow the
     extended parameter part to overlap. Hence we can store the
     definiens of assignments in a tree indexed by the extended
     parameters. The labels of the tree contain the extended parameter
     and an arbitrary value and all elements in the subforest have a
     label with an extended parameter lower than the extended
     parameter at the root node.

-}
data EPNodeLabel a = EPNL { eplabel :: EPExps
                          , nodelabel :: a }

type EPTree a = Tree (EPNodeLabel a)
type EPForest a = Forest (EPNodeLabel a)

makeEPLeaf :: EPExps -> a -> EPTree a
makeEPLeaf eps x = Node { rootLabel = EPNL { eplabel = eps, nodelabel = x }
                        , subForest = [] }

-- | Inserts a node to an 'EPForest'.
insertEPNodeToForest :: EPTree a -- ^ Node to insert
                     -> EPForest a -- ^ Forest to insert the given node in
                     -> EPForest a -- ^ Resulting forest
insertEPNodeToForest n [] = [n]
insertEPNodeToForest n (t:ft) = case insertEPNode n t of
                                  Just t' -> t': ft
                                  Nothing -> t : insertEPNodeToForest n ft
    

-- | Inserts a node to an 'EPTree' and if the nodes are disjoint
--   'Nothing' is returned. Both insert methods return an error if an
--   overlapping occurs.
insertEPNode :: EPTree a -- ^ Node to insert
             -> EPTree a -- ^ Tree to insert the given node in
             -> Maybe (EPTree a) -- ^ Resulting tree
insertEPNode n t =
    case compareEPs (eplabel $ rootLabel n) $ eplabel $ rootLabel t of
      Comparable EQ -> error "insertEPNode: equality overlap"
      Incomparable Overlap -> error "insertEPNode: overlap"
      Incomparable Disjoint -> Nothing
      Comparable GT -> aInB t n
      Comparable LT -> aInB n t
    where
      aInB a b = Just b { subForest = insertEPNodeToForest a (subForest b) }

-- | Returns a graphical representation of the forest.
showEPForest :: (a -> String) -> EPForest a -> String
showEPForest pr =
    let f lbl = showEPs (eplabel lbl)
                ++ case pr $ nodelabel lbl of
                     [] -> []
                     x -> ": " ++ x
    in drawForest . (map $ fmapDefault f)

-- | This function is not a simple map, but inserts the nodes correctly
-- to the tree.
forestFromEPs :: (a -> EPTree b) -> [a] -> EPForest b
forestFromEPs f l = foldr (insertEPNodeToForest . f) [] l

-- ----------------------------------------------------------------------
-- * Handling of Extended Parameter indexed assignments
-- ----------------------------------------------------------------------

-- | A type to store the different definiens of one constant dependent on the
-- extended parameter range
type AssertionMap = Map.Map String (EPForest EXPRESSION)
-- TODO: implement
-- | Adds a command to the assertionmap. Non-assertion commands are ignored.
insertAssignment :: CMD -> AssertionMap -> AssertionMap
insertAssignment = error "TODO"


-- ----------------------------------------------------------------------
-- * Extended Parameter comparison
-- ----------------------------------------------------------------------

{- | Compares two 'EPExps': They are pairwise compared over the common 
     extended parameter names (see also the operator-table in combineCmp).
     This function can be optimized in returning directly disjoint
     once a disjoint subresult encountered.
-}
compareEPs :: EPExps -> EPExps -> EPCompare
compareEPs eps1 eps2 =
    -- choose smaller map for fold, and remember if maps are swapped
    let (eps, eps', sw) = if Map.size eps1 > Map.size eps2
                          then (eps2, eps1, True) else (eps1, eps2, False)
        -- foldfunction
        f k ep (b, c) = let (cmp', c') = 
                                case Map.lookup k eps' of
                                  -- increment the counter
                                  Just ep' -> (compareEP ep ep', c+1)
                                  -- if key not present in reference map then
                                  -- ep < *
                                  _ -> (Comparable LT, c)
                        in (combineCmp b cmp', c')

        -- we fold over the smaller map, which can be more efficient.
        -- We have to count the number of matched parameter names to see if
        -- there are still EPs in eps' which indicates to compare with ">" at
        -- the end of the fold.
        (epc, cnt) = Map.foldWithKey f
                     (Comparable EQ, 0) -- start the fold with "=",
                                        -- the identity element
                     eps -- the smaller map
        epc' = if Map.size eps' > cnt
               then combineCmp (Comparable GT) epc else epc

    -- if the maps were swapped then swap the result
    in if sw then swapCmp epc' else epc'


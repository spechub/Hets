{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Handling of extended parameter relations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

This module defines an ordering on extended parameters and other analysis tools.

Extended parameter relations have the property
 -}

module CSL.EPRelation
 ( EP.compareEP, EP.EPExp, EP.toEPExp, compareEPs, EPExps
 , toEPExps, forestFromEPs, makeEPLeaf, showEPForest, varMapFromSet
 , varMapFromList, boolExps, boolRange, smtPredDef, smtVarDef, smtVars
 , smtGenericStmt, smtEQStmt, smtLEStmt, smtDisjStmt
 , namesInList, EPRange(..), smtAllScripts, smtAllScript, smtScriptHead, smtGenericScript
 , smtEQScript, smtLEScript, smtDisjScript, smtResponse, smtCompare, smtCompare', smtMultiResponse
 )
    where


import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Tree
import Data.List (intercalate, isInfixOf)
import Data.Traversable (fmapDefault)
import System.Process
import System.IO.Unsafe

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
    let outp = intercalate ";"
               $ map showEP $ Map.toList eps
    in if null outp then "*" else outp


-- | Conversion function into the more efficient representation.
toEPExps :: [EXTPARAM] -> EPExps
toEPExps = Map.fromList . mapMaybe toEPExp



data EPRange = Union EPRange EPRange | Intersection EPRange EPRange
             | Difference EPRange EPRange | Atom EPExps

showEPRange :: EPRange -> String
showEPRange re =
    let f s a b = concat ["(", showEPRange a, " ", s, " ", showEPRange b, ")"]
    in case re of
      Union r1 r2 -> f "Un" r1 r2
      Intersection r1 r2 -> f "In" r1 r2
      Difference r1 r2 -> f "\\" r1 r2
      Atom eps -> showEPs eps

instance Show EPRange where
    show = showEPRange

mapRange :: (EPExps -> b) -> EPRange -> [b]
mapRange f re =
    case re of
      Union r1 r2 -> concatMap (mapRange f) [r1, r2]
      Intersection r1 r2 -> concatMap (mapRange f) [r1, r2]
      Difference r1 r2 -> concatMap (mapRange f) [r1, r2]
      Atom eps -> [f eps]

class RangeUtils a where
    names :: a -> Set.Set String

instance RangeUtils EPExps where
    names = Map.keysSet

instance RangeUtils EPRange where
    names = Set.unions . mapRange names

namesInList :: RangeUtils a => [a] -> Set.Set String
namesInList = Set.unions . map names

-- ----------------------------------------------------------------------
-- * SMT output generation
-- ----------------------------------------------------------------------

type VarMap = Map.Map String Int

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromList :: [String] -> VarMap
varMapFromList l = Map.fromList $ zip l $ [1 .. length l]

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromSet :: Set.Set String -> VarMap
varMapFromSet = varMapFromList . Set.toList

-- | Builds a Boolean representation of the 
boolExps :: VarMap -> EPExps -> BoolRep
boolExps m eps = And $ map f $ Map.assocs eps where
    err = error "boolExps: No matching"
    f (k, v) = toBoolRep ("x" ++ show (Map.findWithDefault err k m)) v

boolRange :: VarMap -> EPRange -> BoolRep
boolRange m (Union a b) = Or [boolRange m a, boolRange m b]
boolRange m (Intersection a b) = And [boolRange m a, boolRange m b]
boolRange m (Difference a b) = And [boolRange m a, Not $ boolRange m b]
boolRange m (Atom eps) = boolExps m eps


smtPredDef :: VarMap -> String -> BoolRep -> String
smtPredDef m s b = concat [ "(define ", s, "::(-> "
                          , concatMap (const "int ") $ smtVars m ""
                          , "bool) (lambda ("
                          , concatMap (++ "::int ") $ smtVars m "x", ") "
                          , smtBoolExp b, "))" ]

smtVarDef :: VarMap -> String
smtVarDef m =
    unlines $ map (\ x -> "(define " ++ x ++ " ::int)") $ smtVars m "y"

smtVars :: VarMap -> String -> [String]
smtVars m s = map ((s++) . show) [1 .. Map.size m]

smtGenericStmt :: VarMap -> String -> String -> String -> String
smtGenericStmt m s a b =
    let vl = concat $ map (" "++) $ smtVars m "y"
    in "(assert+ (not (" ++ s ++ " (" ++ a ++ vl ++ ") (" ++ b ++ vl ++ "))))"

smtEQStmt :: VarMap -> String -> String -> String
smtEQStmt m a b = smtGenericStmt m "=" a b

smtLEStmt :: VarMap -> String -> String -> String
smtLEStmt m a b = smtGenericStmt m "=>" a b

smtDisjStmt :: VarMap -> String -> String -> String
smtDisjStmt m a b = 
    let vl = concat $ map (" "++) $ smtVars m "y"
    in "(assert+ (and (" ++ a ++ vl ++ ") (" ++ b ++ vl ++ ")))"


smtAllScript :: VarMap -> EPRange -> EPRange -> String
smtAllScript m r1 r2 =
    unlines [ smtScriptHead m r1 r2
            , smtEQStmt m "A" "B", "(check) (retract 1)"
            , smtLEStmt m "A" "B", "(check) (retract 2)"
            , smtLEStmt m "B" "A", "(check) (retract 3)"
            , smtDisjStmt m "A" "B", "(check)" ]


smtAllScripts :: VarMap -> EPRange -> EPRange -> [String]
smtAllScripts m r1 r2 =
    let h = smtScriptHead m r1 r2
    in [ unlines [h, smtEQStmt m "A" "B", "(check)"]
       , unlines [h, smtLEStmt m "A" "B", "(check)"]
       , unlines [h, smtLEStmt m "B" "A", "(check)"]
       , unlines [h, smtDisjStmt m "A" "B", "(check)"]
       ]

smtScriptHead :: VarMap -> EPRange -> EPRange -> String
smtScriptHead m r1 r2 = unlines [ "(set-arith-only! true)"
                                , smtPredDef m "A" $ boolRange m r1
                                , smtPredDef m "B" $ boolRange m r2
                                , smtVarDef m ]

smtGenericScript :: VarMap -> (VarMap -> String -> String -> String)
                 -> EPRange -> EPRange -> String
smtGenericScript m f r1 r2 = smtScriptHead m r1 r2 ++ "\n" ++ f m "A" "B"

smtEQScript :: VarMap -> EPRange -> EPRange -> String
smtEQScript m r1 r2 = smtGenericScript m smtEQStmt r1 r2

smtLEScript :: VarMap -> EPRange -> EPRange -> String
smtLEScript m r1 r2 = smtGenericScript m smtLEStmt r1 r2

smtDisjScript :: VarMap -> EPRange -> EPRange -> String
smtDisjScript m r1 r2 = smtGenericScript m smtDisjStmt r1 r2

data SMTStatus = Sat | Unsat deriving (Show, Eq)

smtCheck :: VarMap -> EPRange -> EPRange -> IO [SMTStatus]
smtCheck m r1 r2 = smtMultiResponse $ smtAllScript m r1 r2

smtCheck' :: VarMap -> EPRange -> EPRange -> IO [SMTStatus]
smtCheck' m r1 r2 = mapM smtResponse $ smtAllScripts m r1 r2

-- | The result states of the smt solver are translated to the
-- adequate compare outcome. The boolean value is true if the corresponding
-- set is empty.
smtStatusCompareTable :: [SMTStatus] -> (EPCompare, Bool, Bool)
smtStatusCompareTable l =
    case l of
      [Unsat, Unsat, Unsat, x] -> let b = x == Unsat in (Comparable EQ, b, b)
      [Sat, Unsat, Sat, x] -> let b = x == Unsat in (Comparable LT, b, b)
      [Sat, Sat, Unsat, x] -> let b = x == Unsat in (Comparable GT, b, b)
      [Sat, Sat, Sat, Unsat] -> (Incomparable Disjoint, False, False)
      [Sat, Sat, Sat, Sat] -> (Incomparable Overlap, False, False)
      x -> error $ "smtStatusCompareTable: malformed status " ++ show x

smtCompare :: VarMap -> EPRange -> EPRange -> EPCompare
smtCompare m r1 r2 = 
    let (c, _, _) = smtStatusCompareTable $ unsafePerformIO $ smtCheck m r1 r2
    in c

smtFullCompare :: VarMap -> EPRange -> EPRange -> (EPCompare, Bool, Bool)
smtFullCompare m r1 r2 = smtStatusCompareTable $ unsafePerformIO $ smtCheck m r1 r2

smtCompare' :: VarMap -> EPRange -> EPRange -> EPCompare
smtCompare' m r1 r2 =
    let (c, _, _) =  smtStatusCompareTable $ unsafePerformIO
                     $ mapM smtResponse $ smtAllScripts m r1 r2
    in c

smtResponseToStatus :: String -> SMTStatus
smtResponseToStatus s
    | s == "sat" = Sat
    | s == "unsat" = Unsat
    | s == "" = Sat
    | isInfixOf "Error" s = error $ "yices-error: " ++ s
    | otherwise = error $ "unknown yices error"

smtMultiResponse :: String -> IO [SMTStatus]
smtMultiResponse inp = do
  s <- readProcess "yices" [] inp
  return $ map smtResponseToStatus $ lines s

smtResponse :: String -> IO SMTStatus
smtResponse inp = do
  s <- readProcess "yices" [] inp
--  putStrLn "------ yices output ------"
--  putStrLn s
  return $ smtResponseToStatus $
         case lines s of
           [] -> ""
           x:_ ->  x

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


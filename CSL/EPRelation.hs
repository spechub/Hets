{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Handling of extended parameter relations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

This module defines an ordering on extended parameters and provides analysis tools.

 -}

module CSL.EPRelation where


import Control.Monad.Trans
import Control.Monad.Reader
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Tree
import Data.List
import Data.Traversable (fmapDefault)
import System.Process
import System.IO.Unsafe

import CSL.EPBasic
import CSL.TreePO
import CSL.AS_BASIC_CSL
import CSL.ExtendedParameter as EP
    (toBoolRep, showEP, toEPExp, EPExp, compareEP)
import Common.Id (tokStr)

import Common.Doc

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

-- | A more efficient representation of a list of extended parameters, 
-- particularly for comparison
type EPExps = Map.Map String EPExp

prettyEPs :: EPExps -> Doc
prettyEPs eps
    | Map.null eps = text "*"
    | otherwise = brackets $ sepByCommas $ map (text . showEP) $ Map.toList eps

showEPs :: EPExps -> String
showEPs = show . prettyEPs

-- | A star expression is the unconstrained expression corresponding to the
-- whole space of extended parameter values
isStarEP :: EPExps -> Bool 
isStarEP = Map.null

-- | 'isStarEP' lifted for Range expressions.
isStarRange :: EPRange -> Bool 
isStarRange (Atom e) = isStarEP e
isStarRange _ = False

-- | The star range.
starRange :: EPRange
starRange = Atom Map.empty

-- | Conversion function into the more efficient representation.
toEPExps :: [EXTPARAM] -> EPExps
toEPExps = Map.fromList . mapMaybe toEPExp

-- | Sets representing the Parameters for which there is a propagation break
-- (filtered) and for which there is a constraint (constrained)
filteredConstrainedParams :: [EXTPARAM] -> (Set.Set String, Set.Set String)
filteredConstrainedParams = foldl f (Set.empty, Set.empty)
    where f (fs, cs) (EP t "-|" _) = (Set.insert (tokStr t) fs, cs)
          f (fs, cs) (EP t _ _) = (fs, Set.insert (tokStr t) cs)


data EPRange = Union [EPRange] | Intersection [EPRange]
             | Complement EPRange | Atom EPExps | Empty

prettyEPRange :: EPRange -> Doc
prettyEPRange re =
    let f s a b = parens $ hsep [prettyEPRange a, text s, prettyEPRange b]
        g s l = parens $ hsep $ text s : map prettyEPRange l
    in case re of
      Union [r1, r2] -> f "Un" r1 r2
      Intersection [r1, r2] -> f "In" r1 r2
      Complement r -> g "C" [r]
      Union l -> g "Union" l
      Intersection l -> g "Intersection" l
      Empty -> text "Empty"
      Atom eps -> prettyEPs eps


showEPRange :: EPRange -> String
showEPRange = show . prettyEPRange

instance Show EPRange where
    show = showEPRange

-- | Behaves as a map on the list of leafs of the range expression
-- (from left to right)
mapRangeLeafs :: (EPExps -> b) -> EPRange -> [b]
mapRangeLeafs f re =
    case re of
      Union l -> g l
      Intersection l -> g l
      Complement r -> mapRangeLeafs f r
      Atom eps -> [f eps]
      Empty -> []
    where g = concatMap (mapRangeLeafs f)

-- | Maps an EP expression transformer over the given range expression
mapRange :: (EPExps -> EPExps) -> EPRange -> EPRange
mapRange f re =
    case re of
      Union l -> Union $ g l
      Intersection l -> Intersection $ g l
      Complement r -> Complement $ mapRange f r
      Atom eps -> Atom $ f eps
      _ -> re
    where g = map (mapRange f)

class RangeUtils a where
    rangeNames :: a -> Set.Set String

instance RangeUtils EPExps where
    rangeNames = Map.keysSet

instance RangeUtils EPRange where
    rangeNames = Set.unions . mapRangeLeafs rangeNames

namesInList :: RangeUtils a => [a] -> Set.Set String
namesInList = Set.unions . map rangeNames

-- TODO: check the todos at the end for projection-fix


{- | 
   (1) If the arguments are disjoint ->  'Nothing'
   (2) If all extended parameter constraints from the first argument are 
   subsumed by the second argument -> second argument with deleted entries for
   these extended parameters
   (3) Otherwise -> error: the first argument must be subsumed by or disjoint
   with the second one.
-}
projectEPs :: EPExps -> EPExps -> Maybe EPExps
projectEPs e1 e2
    | isStarEP e1 = Just e2
    | otherwise =
        -- take first element from e1 delete it from e1 and proceed with it
        let ((k, v), e1') = Map.deleteFindMin e1
            e2' = Map.delete k e2
        in case Map.lookup k e2 of
             Nothing -> projectEPs e1' e2
             Just v2 ->
                 case compareEP v v2 of
                   Incomparable Disjoint -> Nothing
                   Comparable x -> if x /= GT then projectEPs e1' e2'
                                   else error $ "projectEPs: e1 > e2 "
                                            ++ show (e1,e2)
                   _ -> error  $ "projectEPs: overlap " ++ show (e1,e2)
    

{- |
   Given a range predicate, e.g, A x y z (here with three extended
   parameters), we instantiate it partially with the given
   instantiation, e.g., x=1, and obtain A 1 y z. The new predicate
   does not depend on x anymore and can be built by replacing all
   atomic subexpressions in A which talk about x (1) by the subexpression
   where the constraint for x is removed if the given instantiation
   satisfies this subexpression (e.g., x<10) or (2) by 'Empty' if this
   constraint is not satisfied (e.g., x>1)
-}
projectRange :: EPExps -> EPRange -> EPRange
projectRange e re = simplifyRange $ f re
    where f rexp =
              case rexp of
                Union l -> Union $ map f l
                Intersection l -> Intersection $ map f l
                Complement r -> Complement $ f r
                Atom eps -> case projectEPs e eps of
                              Nothing -> Empty
                              Just eps' -> Atom eps'
                Empty -> Empty
                    

{- | Removes all star- and empty-entries from inside of the range expression.

 Union [,*,] -> *                        (top element)
 Intersection [,*,] -> Intersection [,]  (neutral element)
 Complement * -> Empty                   (bottom element)

 For Empty its the dual behaviour
-}
simplifyRange :: EPRange -> EPRange
simplifyRange re =
    case re of
      Union l -> f [] l
      Intersection l -> g [] l
      Complement r ->
          case simplifyRange r of
            Empty -> starRange
            r' | isStarRange r' -> Empty
               | otherwise -> Complement r'
      _ -> re
    where -- returns either a simplified list or a new expression
      f acc [] = if null acc then Empty else Union acc
      f acc (r:l) =
          case simplifyRange r of
            Empty -> f acc l
            r' | isStarRange r' -> r'
               | otherwise -> f (acc++[r']) l
      g acc [] = if null acc then starRange else Intersection acc
      g acc (r:l) =
          case simplifyRange r of
            Empty -> Empty
            r' | isStarRange r' -> g acc l
               | otherwise -> g (acc++[r']) l

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

-- ----------------------------------------------------------------------
-- * SMT output generation for smt based comparison
-- ----------------------------------------------------------------------

type VarMap = Map.Map String Int

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromList :: [String] -> VarMap
varMapFromList l = Map.fromList $ zip l $ [1 .. length l]

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromSet :: Set.Set String -> VarMap
varMapFromSet = varMapFromList . Set.toList

-- | Builds a Boolean representation from the extended parameter expression
boolExps :: VarMap -> EPExps -> BoolRep
boolExps m eps | isStarEP eps = trueBool
               | otherwise = And $ map f $ Map.assocs eps where
    err = error "boolExps: No matching"
    f (k, v) = toBoolRep ("x" ++ show (Map.findWithDefault err k m)) v

boolRange :: VarMap -> EPRange -> BoolRep
boolRange m (Union l) = Or $ map (boolRange m) l
boolRange m (Intersection l) = And $ map (boolRange m) l
boolRange m (Complement a) = Not $ boolRange m a
boolRange m (Atom eps) = boolExps m eps
boolRange _ Empty = falseBool


-- TODO: put this rather into another module and replace EPRange by BoolRep

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

tripleFst :: (a, b, c) -> a
tripleFst (x, _, _) = x

smtCompare :: VarMap -> EPRange -> EPRange -> IO (EPCompare, Bool, Bool)
smtCompare m r1 r2 = liftM smtStatusCompareTable $ smtCheck m r1 r2

smtCompareUnsafe :: VarMap -> EPRange -> EPRange -> EPCompare
smtCompareUnsafe m r1 r2 = tripleFst $ unsafePerformIO $ smtCompare m r1 r2

smtFullCompareUnsafe :: VarMap -> EPRange -> EPRange -> (EPCompare, Bool, Bool)
smtFullCompareUnsafe m r1 r2 = unsafePerformIO $ smtCompare m r1 r2

smtCompareUnsafe' :: VarMap -> EPRange -> EPRange -> EPCompare
smtCompareUnsafe' m r1 r2 = tripleFst $ smtStatusCompareTable $ unsafePerformIO $ smtCheck' m r1 r2


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

makeEPLeaf :: a -> EPExps -> EPTree a
makeEPLeaf x eps = Node { rootLabel = EPNL { eplabel = eps, nodelabel = x }
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
    case compareEPs ep1 ep2 of
      Comparable EQ -> error $ concat [ "insertEPNode: equality overlap "
                                      , show ep1, " = ", show ep2 ]
      Incomparable Overlap -> error $ concat [ "insertEPNode: overlap "
                                      , show ep1, " = ", show ep2 ]
      Incomparable Disjoint -> Nothing
      Comparable GT -> aInB t n
      Comparable LT -> aInB n t
    where
      aInB a b = Just b { subForest = insertEPNodeToForest a (subForest b) }
      ep1 = eplabel $ rootLabel n
      ep2 = eplabel $ rootLabel t

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
forestFromEPsGen :: (a -> EPTree b) -> [a] -> EPForest b
forestFromEPsGen f l = foldr (insertEPNodeToForest . f) [] l

-- | This function is not a simple map, but inserts the nodes correctly
-- to the tree.
forestFromEPs :: (a -> (b, EPExps)) -> [a] -> EPForest b
forestFromEPs f = forestFromEPsGen $ uncurry makeEPLeaf . f



-- ----------------------------------------------------------------------
-- * Partitions based on 'EPRange'
-- ----------------------------------------------------------------------

class MonadIO m => CompareIO m where
    rangeFullCmp :: EPRange -> EPRange -> m (EPCompare, Bool, Bool)

rangeCmp :: CompareIO m => EPRange -> EPRange -> m EPCompare
rangeCmp x y = liftM tripleFst $ rangeFullCmp x y

type SmtComparer = ReaderT VarMap IO

instance CompareIO SmtComparer where
    rangeFullCmp r1 r2 = do
      vm <- ask
      lift $ smtCompare vm r1 r2

data Partition a = AllPartition a | Partition [(EPRange, a)]

instance Functor Partition where
    fmap f (AllPartition x) = AllPartition $ f x
    fmap f (Partition l) = Partition $ map g l
        where g (er, x) = (er, f x)

refinePartition :: CompareIO m => Partition a -> Partition b
                -> m (Partition (a,b))
refinePartition (AllPartition x) pb = return $ fmap ((,) x) pb
refinePartition (Partition l) pb = error "" -- fmap ((,) x) pb


restrictPartition :: CompareIO m => EPRange -> Partition a -> m (Partition a)
restrictPartition er p
    | isStarRange er = return p
    | otherwise =
        case p of
          AllPartition x -> return $ Partition [(er, x)]
          Partition p' -> liftM Partition $ f p' where
               f [] = return []
               f ((er', x):l) = do
                 cmp <- rangeCmp er er'
                 let er'' = Intersection [er, er']
                 case cmp of
                   Comparable EQ -> return [(er', x)]
                   Comparable LT -> return [(er, x)]
                   Comparable GT -> liftM ((er', x) :) $ f l
                   Incomparable Disjoint -> f l
                   Incomparable Overlap -> liftM ((er'', x) :) $ f l
               




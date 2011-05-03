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
import Data.Char
import Data.List
import Data.Maybe
import Data.Tree
import Data.Traversable (fmapDefault)
import System.IO

import CSL.EPBasic
import qualified CSL.SMTComparison as CMP
import CSL.TreePO
import CSL.AS_BASIC_CSL
import CSL.ExtendedParameter
import Common.Id (tokStr)
import Common.Doc
import Common.DocUtils

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

-- | A more efficient representation of a list of extended parameters, 
-- particularly for comparison
type EPExps = Map.Map String EPExp

evalEPs :: (String -> Int) -> EPExps -> Bool
evalEPs f eps = Map.foldWithKey g True eps where
    g k v b = evalEP (f k) v && b

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


{-| This type represents the domain of the extended parameters. It can have

    0 entries = no restriction

    1 entry = opened rectangle, at least one parameter is one sided restricted

    2 entries = probably closed rectangle, at least one parameter is restricted
                from both sides

    The domain is the intersection of both entries (if there are two)

    The domain is important for building partitions, because the partitions are
    defined only on the domain, not on the unrestricted space.
-}
type EPDomain = [EPExps]

data EPRange = Union [EPRange] | Intersection [EPRange]
             | Complement EPRange | Atom EPExps | Empty

-- | In some cases 'EPRange' can be translated back to 'EPExps'
tryDowncast :: EPRange -> Maybe EPExps
tryDowncast (Complement (Atom x)) =
    if Map.size x == 1 then Just $ Map.map complementEP x else Nothing
tryDowncast (Atom x) = Just x
tryDowncast _ = Nothing


evalRange :: (String -> Int) -> EPRange -> Bool
evalRange f re =
    case re of
      Complement r -> not $ evalRange f r
      Union l -> or $ map (evalRange f) l
      Intersection l -> and $ map (evalRange f) l
      Empty -> False
      Atom eps -> evalEPs f eps


-- | A diagnostic output for 'EPRange' which highlights problems in the
-- internal representation
diagnoseEPRange :: EPRange -> Doc
diagnoseEPRange re =
    let asIfx s l = parens $ fsep $ punctuate (text s) $ map diagnoseEPRange l
        diag s re' = text "DIAG" <>
                     (parens $ text s <> comma <+> diagnoseEPRange re')
    in case re of
      Union [] -> diag "EmptyUnion" Empty
      Union [x] -> diag "SingletonUnion" x
      Union l -> asIfx [' ', chr 8746] l
      Intersection [] -> diag "EmptyIntersection" Empty
      Intersection [x] -> diag "SingletonIntersection" x
      Intersection [x, Complement r] -> asIfx [' ', chr 8726] [x,r]
      Intersection l -> asIfx [' ', chr 8745] l
      Complement r -> text [chr 8705] <> diagnoseEPRange r
      Empty -> text [chr 8709]
      Atom eps -> prettyEPs eps
    

-- | Pretty output for 'EPRange'
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

mkUnion :: [EPRange] -> EPRange
mkUnion [] = error "mkUnion: empty list"
mkUnion [x] = x
mkUnion l = Union l

mkIntersection :: [EPRange] -> EPRange
mkIntersection [] = error "mkIntersection: empty list"
mkIntersection [x] = x
mkIntersection l = Intersection l

showEPRange :: EPRange -> String
showEPRange = show . prettyEPRange

instance Show EPRange where
    show = showEPRange

instance Pretty EPRange where
    pretty = prettyEPRange

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
   atomic subexpressions in A which talk about x

   (1) by the subexpression
   where the constraint for x is removed if the given instantiation
   satisfies this subexpression (e.g., x<10) or

   (2) by 'Empty' if this
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
    case tryDowncast re of
      Just eps -> Atom eps
      _ -> 
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
      f acc [] = if null acc then Empty else mkUnion acc
      f acc (r:l) =
          case simplifyRange r of
            Empty -> f acc l
            r' | isStarRange r' -> r'
               | otherwise -> f (acc++[r']) l
      g acc [] = if null acc then starRange else mkIntersection acc
      g acc (r:l) =
          case simplifyRange r of
            Empty -> Empty
            r' | isStarRange r' -> g acc l
               | otherwise -> g (acc++[r']) l


-- ----------------------------------------------------------------------
-- * Models for 'EPRange' expressions
-- ----------------------------------------------------------------------

data Model a = Model [(Int, Int)] (Map.Map [Int] a)

boolModelChar :: Bool -> Char
boolModelChar b = if b then '*' else ' '

modelToString :: (a -> Char) -> Model a -> String
modelToString f (Model l vm) =
    case l of
      [(a, b)] -> map (f . (\ x -> Map.findWithDefault (error $ "modelToString: elem not in map " ++ show x ++ "\n" ++ (show $ Map.keys vm)) x vm) . (:[])) [a..b] ++ "\n"
      [(a, b), (c, d)] ->
          let g y = map (f . (vm Map.!)) [[x, y]| x <- [a..b]]
          in unlines $ map g [c..d]
      [] -> ""
      _ -> concat ["Cannot output a ", show $ length l, "-dim model"]

modelOf :: Map.Map String (Int, Int) -> EPRange -> Model Bool
modelOf rm re = let
    f l s = l !! (Map.findIndex s rm)
    g (a, b) l = [x : y | y <- l, x <- [a..b]]
    inpl = Map.fold g [[]] rm
    h x = (x, evalRange (f x) re)
    in Model (Map.elems rm) $ Map.fromList $ map h inpl

-- ----------------------------------------------------------------------
-- * Extended Parameter comparison
-- ----------------------------------------------------------------------

{- | Compares two 'EPExps': They are pairwise compared over the common 
     extended parameter names (see also the operator-table in combineCmp).
     This function can be optimized in returning directly disjoint
     once a disjoint subresult encountered.
-}
compareEPs :: EPExps -> EPExps -> SetOrdering
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


{-
  we need to take into account the global constraints on the range of the
  extended parameters, e.g., I in [1,5] or I>=0...
  This complicates the simple comparison and we postpone it for the moment.

-- | We try to decide the relation between the given ranges without using
-- an external decision procedure.
trySimpleFullCmp :: EPRange -> EPRange -> Maybe (SetOrdering, Bool, Bool)
trySimpleFullCmp r1 r2
    | isStarRange r1 && r1 == r2 = Just (Comparable EQ, False, False)
    | r1 == Empty && r1 == r2 = Just (Comparable EQ, True, True)
    | otherwise =
        case map tryDowncast [r1, r2] of
          [Just eps1, Just eps2] -> Just (compareEPs eps1 eps2, False, False)
          _ -> Nothing

-- | Same as 'trySimpleFullCmp' but without deciding if the ranges are empty or not
trySimpleCmp :: EPRange -> EPRange -> Maybe (SetOrdering, Bool, Bool)
trySimpleCmp r1 r2

    | isStarRange r1 = Just (Comparable GT, False, r2 == Empty)
    | isStarRange r2 = Just (Comparable LT, r1 == Empty, False)
-}

-- ----------------------------------------------------------------------
-- * SMT based comparison - utility functions
-- ----------------------------------------------------------------------

-- | Builds a Boolean representation from the extended parameter expression.
-- Variable names are composed from the string "x" together with an integer.
boolExps :: CMP.VarMap -> EPExps -> BoolRep
boolExps m eps | isStarEP eps = trueBool
               | otherwise = And $ map f $ Map.assocs eps where
    err = error "boolExps: No matching"
    f (k, v) = toBoolRep ("x" ++ show (Map.findWithDefault err k m)) v

boolRange :: CMP.VarMap -> EPRange -> BoolRep
boolRange m (Union l) = Or $ map (boolRange m) l
boolRange m (Intersection l) = And $ map (boolRange m) l
boolRange m (Complement a) = Not $ boolRange m a
boolRange m (Atom eps) = boolExps m eps
boolRange _ Empty = falseBool

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

-- | Inserts a node to an 'EPForest'. We need to check if the new node subsumes
-- a nonempty subset of the given forrest.
insertEPNodeToForest :: EPTree a -- ^ Node to insert, assumed to have an
                                 -- empty subforest (the subforest is ignored)
                     -> EPForest a -- ^ Forest to insert the given node in
                     -> EPForest a -- ^ Resulting forest
insertEPNodeToForest n [] = [n]
insertEPNodeToForest n ft@(t:rft) = 
    if null ssf then
        case insertEPNode n t of
          Just t' -> t': rft
          Nothing -> t : insertEPNodeToForest n rft
    else n{subForest = ssf}:nssf
        where (ssf, nssf) = getSubsumedForest (eplabel $ rootLabel n) ft

-- | Splits the given forest to a by the 'EPExps' subsumed part and a not
-- subsumed part. Errors are reported in situations which would lead to invalid
-- forests when used in the 'insertEPNodeToForest'-method.
getSubsumedForest :: EPExps -- ^ Expression to be checked against the forest
                  -> EPForest a -- ^ Forest to be checked for being subsumed
                  -> (EPForest a, EPForest a) -- ^ Subsumed forest and the rest
getSubsumedForest eps ft = partition p ft where
    ep2 = eplabel . rootLabel
    p t = case compareEPs eps (ep2 t) of
            Comparable EQ ->
                error $ concat [ "getSubsumedForest: equality "
                               , "overlap ", show $ prettyEPs eps, " = "
                               , show $ prettyEPs (ep2 t) ]
            Incomparable Overlap ->
                error $ concat [ "getSubsumedForest: overlap "
                               , show $ prettyEPs eps, " = "
                               , show $ prettyEPs (ep2 t) ]
            Comparable GT -> True
            _ -> False

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

instance Pretty a => Pretty (EPNodeLabel a) where
    pretty x = parens $ prettyEPs (eplabel x) <> colon <+> pretty (nodelabel x)

instance Pretty a => Show (EPNodeLabel a) where
    show = show . pretty

-- ----------------------------------------------------------------------
-- * Partitions based on 'EPRange'
-- ----------------------------------------------------------------------

class MonadIO m => CompareIO m where
    rangeFullCmp :: EPRange -> EPRange -> m (SetOrdering, Bool, Bool)
    logMessage :: String -> m ()
    logMessage _ = return ()

rangeCmp :: CompareIO m => EPRange -> EPRange -> m SetOrdering
rangeCmp x y = liftM fst3 $ rangeFullCmp x y where
    fst3 (a, _, _) = a

type SmtComparer = ReaderT CMP.VarEnv IO

execSMTComparer :: CMP.VarEnv -> SmtComparer a -> IO a
execSMTComparer ve smt = runReaderT smt ve

instance CompareIO SmtComparer where
    logMessage s = do
      ve <- ask
      case CMP.loghandle ve of
        Just hdl -> liftIO $ hPutStrLn hdl s
        _ -> return ()

    rangeFullCmp r1 r2 = do
            ve <- ask
            let vm = CMP.varmap ve
            lift $ CMP.smtCompare ve (boolRange vm r1) $ boolRange vm r2

data Partition a = AllPartition a | Partition [(EPRange, a)]

instance Show a => Show (Partition a) where
    show p = show $ prettyPartition (text . show) p

prettyPartition :: (a -> Doc) -> Partition a -> Doc
prettyPartition f (AllPartition x) = braces $ braces $ f x
prettyPartition f (Partition l) = braces $ sepByCommas $ map (braces . g) l
    where g (r, x) = f x <+> text "|" <+> prettyEPRange r


instance Pretty a => Pretty (Partition a) where
    pretty (AllPartition x) = text "AllPartition:" <+> pretty x
    pretty (Partition l) = text "Partition:" <+>
                           ppPairlist pretty pretty braces vcat f l
                               where f a b = parens $ a <+> text "|" <+> b

instance Functor Partition where
    fmap f (AllPartition x) = AllPartition $ f x
    fmap f (Partition l) = Partition $ map g l
        where g (er, x) = (er, f x)

{- | Two partitions are refined to a result partition which is finer than each
   of the input partitions.
   
   The annotations of the new partition are as follows:
   
   a set @x@ in the new partition gets the annotation @(a,b)@ where @x'@ comes
   from the first partition and is annotated with @a@ and @x''@ comes
   from the second partition and is annotated with @b@ and @x@ is a subset of
   both, @x'@ and @x''@.
-}
refinePartition :: (CompareIO m, Pretty a, Pretty b) => Partition a
                -> Partition b -> m (Partition (a,b))
refinePartition (AllPartition x) pb = return $ fmap ((,) x) pb
refinePartition pa (AllPartition x) = return $ fmap (flip (,) x) pa
refinePartition (Partition l) (Partition l') =
   liftM (Partition . concat) $ mapM (f l') l
   where
    f [] _ = return []
    f ((er', y):ll) a@(er, x) = do
      cmp <- rangeCmp er er'
      let er'' = Intersection [er, er']
      case cmp of
        Comparable GT -> liftM ((er', (x, y)) :) $ f ll a
        Incomparable Disjoint -> f ll a
        Incomparable Overlap -> liftM ((er'', (x, y)) :) $ f ll a
        -- this case combine LT and EQ
        _ -> return [(er, (x, y))]


{- | The partition is restricted explicitly to the given range, that is,
   each set of the partition is intersected with the set from the range
   and the empty sets are filtered out.
-}
restrictPartition :: (CompareIO m, Pretty a) =>
                     EPRange -> Partition a -> m (Partition a)
restrictPartition er p
    | isStarRange er = return p
    | otherwise =
        case p of
          AllPartition x -> return $ Partition [(er, x)]
          Partition p' -> liftM Partition $ f p'
              where
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



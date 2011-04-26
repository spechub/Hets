{- |
Module      :  $Header$
Description :  Definition of Dependency Graph with utils
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Definition of Dependency Graph and utils to be applied to dependency stores
-}


module CSL.DependencyGraph
    where

import Common.Doc
import Common.DocUtils

import CSL.AS_BASIC_CSL
import CSL.Sign as Sign

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

-- * Dependency Graph datatype for various algorithms on Dependency Graphs

data DepGraph a b c = DepGraph
    { dataMap :: Map.Map a
                 ( b         -- the annotation
                 , Set.Set a -- the direct successors (smaller elements)
                 , Set.Set c -- the direct predecessors (bigger elements)
                 )
    -- function returning for a given element and value the predecessors
    -- of this element
    , getPredecessors :: a -> b -> [c]
    -- function returning for a given element and value the predecessors
    -- of this element
    , getKey :: c -> a
    }

instance (Show a, Show b, Show c) => Show (DepGraph a b c) where
    show = show . dataMap

depGraphLookup :: Ord a =>
                  DepGraph a b c -> a -> Maybe (b, Set.Set a, Set.Set c)
depGraphLookup gr x = Map.lookup x $ dataMap gr

prettyDepGraph :: (a -> Doc) -> (b -> Doc) -> (c -> Doc) -> DepGraph a b c 
               -> Doc
prettyDepGraph pa pb pc gr =
    ppMap pa pf ((text "DepGraph" <+>) . braces) vcat f $ dataMap gr where
        f a b = a <> text ":" <+> b
        pf (v, dss, dps) =
            ps pa dss <+> text " << x << " <+> ps pc dps <> text ":" <+> pb v
        ps g = braces . (sepByCommas . map g) . Set.toList


instance (Pretty a, Pretty b, Pretty c) => Pretty (DepGraph a b c) where
    pretty = prettyDepGraph pretty pretty pretty


emptyDepGraph :: (a -> b -> [c]) -> (c -> a) -> DepGraph a b c
emptyDepGraph f pf = DepGraph { dataMap = Map.empty, getPredecessors = f
                              , getKey = pf }


-- TODO: merge the type Rel2 and DepGraph in order to work only on the
-- new type, and implement a construction of this graph from a list
-- without the necessity to order the elements first.

-- | It is important to have the elements given in an order with
-- biggest elements first (elements which depend on nothing)
depGraphFromDescList :: (Ord a, Ord c) => (a -> b -> [c]) -> (c -> a) -> [(a,b)]
                     -> DepGraph a b c
depGraphFromDescList f pf = foldl g (emptyDepGraph f pf) where
    g x (y, z) = updateGraph x y z

maybeSetUnions :: Ord a => Set.Set (Maybe (Set.Set a)) -> Set.Set a
maybeSetUnions s = Set.fold f Set.empty s where
    f mS s' = maybe s' (Set.union s') mS

upperLevel :: (Ord a, Ord c) => DepGraph a b c -> Set.Set a -> Set.Set c
upperLevel gr = maybeSetUnions . Set.map f where
    f a = fmap g $ Map.lookup a $ dataMap gr
    g (_, _, dps) = dps

lowerLevel :: Ord a => DepGraph a b c -> [a] -> Set.Set a
lowerLevel gr = Set.unions . mapMaybe f where
    f a = fmap g $ Map.lookup a $ dataMap gr
    g (_, dss, _) = dss


setFilterLookup :: (Ord a, Ord b, Ord d, Show a) =>
                   (d -> a) -- ^ projection function
                -> (a -> b -> Bool) -- ^ filter predicate
                -> DepGraph a b c -- ^ dependency graph for lookup
                -> Set.Set d -- ^ filter this set
                -> Set.Set (d,b)
setFilterLookup pf fp gr s = Set.map h $ Set.filter g $ Set.map f s where
    f x = (x, fmap ( \ (v, _, _) -> v ) $ Map.lookup (pf x) $ dataMap gr)
    g (x, Just val) = fp (pf x) val
    g _ = False
    h (x, Just val) = (x, val)
    h _ = error "setFilterLookup: Impossible case"


lowerUntil :: (Pretty a, Ord a, Ord b, Show a) =>
              (a -> b -> Bool) -- ^ cut-off predicate
           -> DepGraph a b c -- ^ dependency graph to be traversed
           -> [a] -- ^ compare entries to this element
           -> Set.Set (a,b)
lowerUntil _ _ [] = Set.empty
lowerUntil cop gr al =
    let s = lowerLevel gr al
        cop' x = not . cop x
        s' = setFilterLookup id cop' gr s
        s'' = lowerUntil cop gr $ map fst $ Set.toList s'
    in Set.union s' s''

upperUntil :: (Ord a, Ord b, Ord c, Show a) =>
              (a -> b -> Bool) -- ^ cut-off predicate
           -> DepGraph a b c -- ^ dependency graph to be traversed
           -> Set.Set a -- ^ compare entries to these elements
           -> Set.Set (c,b)
upperUntil cop gr es
    | Set.null es = Set.empty
    | otherwise =
        let s = upperLevel gr es
            cop' x = not . cop x
            s' = setFilterLookup (getKey gr) cop' gr s
            s'' = upperUntil cop gr $ Set.map (getKey gr . fst) s'
        in Set.union s' s''

-- | Reflexive version of 'upperUntil'
upperUntilRefl :: (Ord a, Ord b, Show a) =>
                  (a -> b -> Bool) -- ^ cut-off predicate
               -> DepGraph a b a -- ^ dependency graph to be traversed
               -> Set.Set a -- ^ compare entries to these elements
               -> Set.Set (a,b)
upperUntilRefl cop gr es
    | Set.null es = Set.empty
    | otherwise =
        Set.union (setFilterLookup (getKey gr) (const $ const True) gr es)
               $ upperUntil cop gr es


-- | Updates the depgraph at the given key with the update function.
-- The dependencies are NOT recomputed. No new elements are added to the graph.
updateValue :: Ord a => DepGraph a b c -> (b -> b) -> a -> DepGraph a b c
updateValue gr uf key = gr { dataMap = Map.adjust uf' key $ dataMap gr } where
    uf' (x, y, z) = (uf x, y, z)


-- | Updates the depgraph at the given key with the new value.
-- The dependencies are recomputed. If the key does not exist in the graph
-- it is added to the graph.
updateGraph :: (Ord a, Ord c) => DepGraph a b c -> a -> b -> DepGraph a b c
updateGraph gr key val =
    -- update the pred-set of all smaller entries
    let (mOv, nm) = Map.insertLookupWithKey f key nval $ dataMap gr
        npl = getPredecessors gr key val
        nval = (val, Set.empty, Set.fromList npl)
        f _ (v', _, nps) (_, oss, _) = (v', oss, nps)
        nm' = case mOv of 
                Just (_, _, ops) ->
                    Set.fold rmFromSucc nm ops
                _ -> nm
        rmFromSucc c m = Map.adjust g1 (getKey gr c) m
        g1 (x, dss, dps) = (x, Set.delete key dss, dps)
        nm'' = foldl insSucc nm' npl
        insSucc m c = Map.adjust g2 (getKey gr c) m
        g2 (x, dss, dps) = (x, Set.insert key dss, dps)
    in gr { dataMap = nm'' }

data DepGraphAnno a = DepGraphAnno
    { annoDef :: AssDefinition
    , annoVal :: a } deriving (Show, Eq, Ord)

instance Pretty a => Pretty (DepGraphAnno a) where
    pretty (DepGraphAnno { annoDef = def, annoVal = av }) =
        braces $ pretty def <> text ":" <+> pretty av

type AssignmentDepGraph a =
    DepGraph ConstantName (DepGraphAnno a) ConstantName

assDepGraphFromDescList :: (ConstantName -> AssDefinition -> a)
                        -> [(ConstantName, AssDefinition)]
                        -> AssignmentDepGraph a
assDepGraphFromDescList f l = depGraphFromDescList getPs id $ map g l where
    g (cn, ad) = (cn, DepGraphAnno { annoDef = ad, annoVal = f cn ad })
    getPs _ = map SimpleConstant . Set.toList . setOfUserDefined . getDefiniens
              . annoDef


{- OLD, using instantiated constants
type AssignmentDepGraph a =
    DepGraph ConstantName (DepGraphAnno a) InstantiatedConstant

assDepGraphFromDescList :: (ConstantName -> AssDefinition -> a)
                        -> [(ConstantName, AssDefinition)]
                        -> AssignmentDepGraph a
assDepGraphFromDescList f l = depGraphFromDescList getPs constName $ map g l where
    g (cn, ad) = (cn, DepGraphAnno { annoDef = ad, annoVal = f cn ad })
    getPs _ = Set.toList . setOfUserDefinedICs . getDefiniens . annoDef
-}

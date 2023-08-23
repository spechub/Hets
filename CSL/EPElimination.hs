{- |
Module      :  ./CSL/EPElimination.hs
Description :  The extended parameter elimination procedure
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

The elimination procedure for extended parameters
-}


module CSL.EPElimination
    where

import Common.Id

import CSL.AS_BASIC_CSL
import CSL.ASUtils
import CSL.Fold
import CSL.EPRelation

import CSL.GuardedDependencies

import Control.Monad
import qualified Data.Tree as Tr
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

{- | Transforms the old guards where inclusion overlapping was allowed into
disjoint new guards. -}
analyzeGuarded :: Guarded [EXTPARAM] -> Guarded EPRange
analyzeGuarded x =
    let f grd = (grd, toEPExps $ range grd)
        -- builds a forest mirroring the inclusion relation of the guard ranges
        frst = forestFromEPs f $ guards x
        -- compute the new range information with the disjointness property
        g l rl sf =
            let nodeRg = Atom $ eplabel rl
                newRg = case map (Atom . eplabel . Tr.rootLabel) sf of
                          [] -> nodeRg
                          {- we make nodeRg disjoint with its children
                          by removing the union of the children from it -}
                          rgl -> if isStarEP (eplabel rl)
                                 then Complement $ mkUnion rgl
                                 else Intersection
                                          [nodeRg, Complement $ mkUnion rgl]
            in (nodelabel rl) { range = newRg } : l
        newguards = foldForest g [] frst
    in x { guards = newguards }

{- | Folds the forest in top-down direction constructing the accumulator
from the labels and children of each node. -}
foldForest :: (b -> a -> Tr.Forest a -> b) -> b -> Tr.Forest a -> b
foldForest f = foldl g where
     g x tr = let sf = Tr.subForest tr
              in foldl g (f x (Tr.rootLabel tr) sf) sf


-- ** Dependency Sorting

{- | Returns a dependency sorted list of constants with their guarded
definitions. Requires as input an analyzed Assignment store:
@(fmap analyzeGuarded . fst . splitAS)@ produces an adequate input. -}
dependencySortAS :: GuardedMap EPRange -> [(String, Guarded EPRange)]
dependencySortAS grdm = mapMaybe f $ topsortDirect $ getDependencyRelation grdm
    where f x = fmap ((,) x) $ Map.lookup x grdm


type Rel2 a = Map.Map a (Set.Set a)
type BackRef a = Map.Map a [a]

{- | @r dependsOn r'@ if @r'@ occurs in the definition term of @r@. In this case
the set which corresponds to the 'Map.Map' entry of @r@ contains @r'@. -}
getDependencyRelation :: GuardedMap a -> Rel2 String
getDependencyRelation gm = Map.fold f dr dr where
    f s m = Map.union m $ Map.fromAscList
            $ map (flip (,) Set.empty) $ Set.toAscList s
    dr = Map.map g gm
    g grdd = Set.unions $ map (setOfUserDefined . definition) $ guards grdd

getBackRef :: Ord a => Rel2 a -> BackRef a
getBackRef d =
    let uf k n = Map.insertWith (++) n [k]
        -- for each entry in the set insert k into the list
        f k s m = Set.fold (uf k) m s
    -- from each entry in d add entries in the map
    in Map.foldrWithKey f Map.empty d


topsortDirect :: (Show a, Ord a) => Rel2 a -> [a]
topsortDirect d = topsort d $ getBackRef d

{- | This function is based on the Kahn-algorithm. It requires a representation
of a relation which has for each entry of the domain an entry in the map. -}

{- E.g., 1 |-> {2}, 2 |-> {3, 4} is not allowed because the entries
3 |-> {}, 4 |-> {} are missing -}
topsort :: (Show a, Ord a) => Rel2 a -> BackRef a -> [a]
topsort d br =
 let f d' acc []
         | Map.null d' = acc
         | otherwise =
             let (s, v) = Map.findMin d'
             in error $ concat [ "topsort: Dependency relation contains cycles "
                               , show s, " -> ", show v ]
     f d' acc (n : l) =
         let cl = Map.findWithDefault [] n br
             (nl, d'') = foldl (remEdge n) ([], d') cl
         in f d'' (acc ++ [n]) $ l ++ nl
     uf n a = let b = Set.delete n a in if Set.null b then Nothing else Just b
     -- returns a new list of empty-nodes and a new def-map
     remEdge n (nl, m) s = let c = Map.size m
                               m' = Map.update (uf n) s m
                           in (if Map.size m' < c then s : nl else nl, m')
     (me, mne) = Map.partition Set.null d
 in f mne [] $ Map.keys me


-- ** Extended Parameter Elimination


{- |
   Given a dependency ordered list of constant definitions we compute all
   definitions not depending on extended parameter propagation, therefore
   eliminating them. For each constant we produce probably many new constants
   that we call elim-constants. The definition of elim-constant N can be
   looked up in @(guards x)!!N@.
-}
epElimination :: CompareIO m => [(String, Guarded EPRange)]
              -> m [(String, Guarded EPRange)]
epElimination = f Map.empty
    {- for efficient lookup, we build a map in addition to the list containing
    the same information -}

    where
      f _ [] = return []
      f m ((s, g) : l) = do
        newguards <- liftM concat $ mapM (eliminateGuard m) $ guards g
        let g' = g { guards = newguards }
        liftM ((s, g') :) $ f (Map.insert s g' m) l

{- |
   The given map already contains only elim-constants. We extract the
   (partly instantiated) constants from the definition in the guard and
   create a partition from their guarded entry in the map. We use
   'refineDefPartitions' to create the refinement and from this we produce
   the new guards.
-}
eliminateGuard :: CompareIO m => GuardedMap EPRange -> Guard EPRange
               -> m [Guard EPRange]
eliminateGuard m grd = do
    let f s epl _ = restrictPartition (range grd)
                    $ case Map.lookup s m of
                        Just grdd -> partitionFromGuarded epl grdd
                        Nothing -> AllPartition 0
        h pim = foldTerm passRecord { foldOp = const $ mappedElimConst pim }
                $ definition grd
        g (er, pim) = grd { range = er, definition = h pim }
    logMessage $ "eliminating Guard " ++ assName grd
    partMap <- mapUserDefined f $ definition grd
    rePart <- refineDefPartitions partMap
    case rePart of
      AllPartition x -> return [g (range grd, x)]
      Partition l ->
          -- for each entry in the refined partition create a new guard
          return $ map g l


{- | Helper function of 'eliminateGuard' for substitution of operatornames
by mapped entries given in the @'Map.Map' 'PIConst' 'Int'@. -}
mappedElimConst :: Map.Map PIConst Int
                -> OPID  -- ^ the original operator id
                -> [EXTPARAM] -- ^ the extended parameter instantiation
                -> [EXPRESSION] -- ^ the new arguments
                -> Range -- ^ the original range
                -> EXPRESSION
mappedElimConst m oi e = Op newOi []
    where err = error $ "mappedElimConst: No entry for " ++ show oi
          i = Map.findWithDefault err (mkPIConst (simpleName oi) e) m
          newOi = case oi of
                    OpUser c -> OpUser $ toElimConst c i
                    _ -> oi

{- | Returns the simplified partition representation of the 'Guarded' object
probably instantiated by the provided extended parameter list. -}
partitionFromGuarded :: [EXTPARAM] -> Guarded EPRange -> Partition Int
partitionFromGuarded epl grdd =
    case guards grdd of
      [] -> error "partitionFromGuarded: empty guard list"
      [grd] | isStarRange $ range grd -> AllPartition 0
            | otherwise ->
                error $ "partitionFromGuarded: single guard not exhaustive: "
                      ++ show grd

      grds ->
        {- it is crucial here that the zipping takes place with the
           original guard list, otherwise the indexes doesn't
           match their definitions -}
        Partition $ mapMaybe f $ zip grds [0 ..] where
            ep = toEPExps epl
            f (a, b) | null epl = Just (range a, b)
                     | otherwise = case projectRange ep $ range a of
                                     Empty -> Nothing
                                     x -> Just (x, b)


-- | A partially instantiated constant
type PIConst = (String, Maybe EPExps)

mkPIConst :: String -> [EXTPARAM] -> PIConst
mkPIConst s epl = (s, if null epl then Nothing else Just $ toEPExps epl)

{- | Returns a map of user defined (partially instantiated) constants
to the result of this constant under the given function. -}
mapUserDefined :: Monad m => (String -> [EXTPARAM] -> [EXPRESSION] -> m a)
                   -> EXPRESSION -> m (Map.Map PIConst a)
mapUserDefined f = g Map.empty
    where
      g m x =
       case x of
         Op oi@(OpUser _) epl al _ -> do
             v <- f (simpleName oi) epl al
             let pic = mkPIConst (simpleName oi) epl
                 m' = Map.insert pic v m
             foldM g m' al
         -- handle also non-userdefined ops.
         Op _ _ al _ -> foldM g m al
         -- ignoring lists (TODO: they should be removed soon anyway)
         _ -> return m

{- |
   Given a map holding for each constant, probably partly instantiated,
   a partition labeled by the corresponding elim-constants we build a
   partition which refines each of the given partitions labeled by a mapping
   of partly instantiated constants to the corresponding elim-constant
-}
refineDefPartitions :: CompareIO m => Map.Map PIConst (Partition Int)
                    -> m (Partition (Map.Map PIConst Int))
refineDefPartitions =
    foldM refineDefPartition (AllPartition Map.empty) . Map.toList

refineDefPartition :: CompareIO m => Partition (Map.Map PIConst Int)
                   -> (PIConst, Partition Int)
                   -> m (Partition (Map.Map PIConst Int))
refineDefPartition pm (c, ps) = do
    logMessage $ "refining partition for " ++ show c
    liftM (fmap $ uncurry $ Map.insert c) $ refinePartition ps pm


-- * Various Outputs of Guarded Assignments

-- | All in the given AssignmentStore undefined constants
undefinedConstants :: GuardedMap a -> Set.Set String
undefinedConstants gm =
     Map.keysSet
            $ Map.difference (Map.filter Set.null $ getDependencyRelation gm) gm

{- | Turn the output of the elimination procedure into single (unguarded)
(probably functional) definitions. Respects the input order of the list. -}
getElimAS :: [(String, Guarded EPRange)] ->
             [(ConstantName, AssDefinition)]
getElimAS = concatMap f where
    f (s, grdd) = zipWith (g s $ argvars grdd) [0 ..] $ guards grdd
    g s args i grd = (ElimConstant s i, mkDefinition args $ definition grd)


-- TODO: implement the map-output
getElimASWithMap :: [(String, Guarded EPRange)] ->
                    ([(ConstantName, AssDefinition)],
                     Map.Map ConstantName EPRange)
getElimASWithMap gds = (getElimAS gds, Map.empty)

{- | Return the assignments in output format of 'getElimAS' but for assignments
not beeing extended parameter eliminated (for simple specs). -}
getSimpleAS :: [(String, Guarded EPRange)] ->
             [(ConstantName, AssDefinition)]
getSimpleAS = map f where
    f (s, grdd) =
        case guards grdd of
          [grd] -> g s (argvars grdd) grd
          _ -> error $ "getSimpleAS: only singleton guards supported: "
               ++ show grdd
    g s args grd = (SimpleConstant s, mkDefinition args $ definition grd)

-- | The elim-constant to 'EPRange' mapping.
elimConstants :: [(String, Guarded EPRange)] ->
             [(String, Map.Map ConstantName EPRange)]
elimConstants = map f where
    f (s, grdd) = (s, Map.fromList $ zipWith (g s) [0 ..] $ guards grdd)
    g s i grd = (ElimConstant s i, range grd)

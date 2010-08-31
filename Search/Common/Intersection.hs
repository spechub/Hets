{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Search.Common.Intersection where

import Search.Utils.SetMap (maybeUnion)
import Data.List (elemIndex,nub,sort)
import Data.Set (fromList,toList, difference)
import Data.Map (unions)
import Search.Common.Data
import Search.Common.Select (constructRenaming)
import Data.Graph.Inductive.Query.Indep (indep)
import Data.Graph.Inductive.Graph (mkUGraph,Node,Edge)
import Data.Graph.Inductive.Tree

type Intersection f s p = ([Profile f s p],Renaming p)

data MinRenaming f s p = 
    MinRen {profile :: Profile f s p,
            renaming :: Renaming p,
            linePair :: (LineNr,LineNr)} deriving (Show,Eq)


intersect :: (Eq s, Eq f,Ord s, Ord f,Ord p, Read p, Show p) =>
             (FilePath -> IO ([Profile f s p]))
          -> FilePath
          -> FilePath
          -> IO (Intersection f s p)
intersect readFromFile t1 t2 =
    do p1 <- readFromFile t1
       p2 <- readFromFile t2
       return (theoryIntersection p1 p2)


theoryIntersection :: (Eq s, Eq f,Read p,Ord s, Ord f, Ord p)
                      => [Profile f s p]
                   -> [Profile f s p]
                   -> Intersection f s p
theoryIntersection ps1 ps2 = (intersection,renaming')
    where mappings = takeJust [minTrans p1 p2 | p1 <- ps1, p2 <- ps2]
          compatibles = [(v1,v2) | v1 <- mappings, v2 <- mappings,
                                   compatible (renaming v1) (renaming v2)]
          nodes = [0..((length mappings)-1)]
          toId v = case elemIndex v mappings of (Just i) -> i
          toEdges (v1,v2) = (toId  v1, toId v2)
          maxClique = findMaximumClique nodes (map toEdges compatibles)
          minRenaming = map (mappings!!) maxClique
          renaming' = unions (map renaming minRenaming)
          intersection = sort $ nub $ map profile minRenaming


compatible :: (Ord p) => Renaming p -> Renaming p -> Bool
compatible r1 r2 =
    case maybeUnion r1 r2
    of (Just _) -> True
       Nothing -> False

match :: (Eq s,Ord p, Read p) => Profile f s p -> Profile f s p -> Maybe (MinRenaming f s p)
match p1 p2 =
    if skeleton p1 /= skeleton p2
    then Nothing
    else case constructRenaming (parameter p1) (parameter p2)
         of (Just renaming) -> Just (MinRen p1 renaming (lineNr p1,lineNr p2))
            _ -> Nothing

minTrans :: (Eq s,Read p, Ord p) =>
            Profile f s p 
         -> Profile f s p
         -> Maybe (MinRenaming f s p)
minTrans p1 p2 =
    case match p1 p2
    of (Just r) -> if bijective r then Just r else Nothing
       _ -> Nothing

bijective :: MinRenaming f s p -> Bool
bijective _ = True -- tmp!!!





takeJust :: [Maybe a] -> [a]
takeJust ((Just x):xs) = x:(takeJust xs)
takeJust (Nothing:xs) = takeJust xs
takeJust [] = []

{- 
   graph theoretic functions
-}

findMaximumClique :: [Node] -> [Edge] -> [Node]
findMaximumClique nodes edges = indep dualGraph
    where dualGraph = mkUGraph nodes (mkDualEdges nodes edges)::Gr () ()

mkDualEdges nodes edges = toList $ difference (fromList allEdges) (fromList edges)
    where allEdges = [(n1,n2) | n1 <- nodes, n2 <- nodes]

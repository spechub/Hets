{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Useful functions missing in the graph library fgl.
-}

module Common.GraphUtils where

import Common.Lib.Graph

import Data.List (nub)
-- import IOExts

-- |
-- transitive closure on Graphs
transitiveClosure :: b -> Graph a b -> Graph a b
transitiveClosure el g = insEdges (concatMap mkEdges $ nodes g) g
    where mkEdges n = zip3 (repeat n) 
		           (filter (notSuc n) $ reachableNodes g n)
			   (repeat el)
	  notSuc n x = not $ x `elem` suc g n

transitiveClosureU :: Graph a () -> Graph a ()
transitiveClosureU = transitiveClosure ()

reachableNodes :: Graph a b -> Node -> [Node]
reachableNodes g sn = nub $ collectReachableNodes [sn] []
    where collectReachableNodes []     _    = []
	  collectReachableNodes (v:vs) seen = 
	      sucs ++ (collectReachableNodes (vs ++ sucs) seen')
	      where sucs  = filter (\x -> not $ x `elem` seen') $ nub $ suc g v
		    --  self  = if sn `elem` sucgv then [sn] else []
		    seen' = v:seen

reflexiveClosure :: b -> Graph a b -> Graph a b
reflexiveClosure el g = insEdges (filter notSuc $ map mkEdge $ nodes g) g
    where mkEdge n = (n,n,el)
	  notSuc (n,_,_) = not $ n `elem` suc g n
reflexiveClosureU :: Graph a () -> Graph a ()
reflexiveClosureU = reflexiveClosure ()

labelEdges :: (b->b) ->  b -> [Edge] -> (b,[LEdge b])
labelEdges f ilab ps = 
    (f ilab, map (\(s,t) -> (s,t,ilab)) ps) 

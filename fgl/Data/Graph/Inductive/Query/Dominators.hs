module Data.Graph.Inductive.Query.Dominators(
    dom
) where

import Data.List
import Data.Graph.Inductive.Graph


type DomSets = [(Node,[Node],[Node])]


intersection :: [[Node]] -> [Node]
intersection cs = foldr intersect (head cs) cs

getdomv :: [Node] -> DomSets -> [[Node]]
getdomv vs  ds = [z|(w,_,z)<-ds,v<-vs,v==w]

builddoms :: DomSets -> [Node] -> DomSets
builddoms ds []     = ds
builddoms ds (v:vs) = builddoms ((fs++[(n,p,sort(n:idv))])++(tail rs)) vs
                      where idv     = intersection (getdomv p ds)
                            (n,p,_) = head rs
                            (fs,rs) = span (\(x,_,_)->x/=v) ds

domr :: DomSets -> [Node] -> DomSets
domr ds vs|xs == ds  = ds
          |otherwise = builddoms xs vs
           where xs = (builddoms ds vs)

{-|
Finds the dominators relationship for a given graph and an initial
node. For each node v, it returns the list of dominators of v.
-}
dom :: Graph gr => gr a b -> Node -> [(Node,[Node])]
dom g u = map (\(x,_,z)->(x,z)) (domr ld n')
           where ld    = (u,[],[u]):map (\v->(v,pre g v,n)) (n')
                 n'    = n\\[u]
                 n     = nodes g



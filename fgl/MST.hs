--
--  MST.hs -- Minimum Spanning Tree Algorithms  (c) 2000 by Martin Erwig
--
module MST (
   msTreeAt,msTree,                               -- minimum spanning tree
   msPath                                         -- path in mst
) where

import Graph
import qualified Heap as H
import RootPath


newEdges :: Ord b => LPath b -> Context a b -> [H.Heap (LPath b)]
newEdges p (_,_,_,s) = map (\(l,v)->H.unit ((v,l):p)) s

prim :: Real b => H.Heap (LPath b) -> Graph a b -> LRTree b
prim h g | H.isEmpty h || isEmpty g = []
prim h g =
    case match v g of
         (Just c,g')  -> p:prim (H.mergeAll (h':newEdges p c)) g'
         (Nothing,g') -> prim h' g'  
    where (p@((v,d):_),h') = H.splitMin h

msTreeAt :: Real b => Node -> Graph a b -> LRTree b
msTreeAt v g = prim (H.unit [(v,0)]) g

msTree :: Real b => Graph a b -> LRTree b
msTree g = msTreeAt v g where ((_,v,_,_),_) = matchAny g

msPath :: Real b => LRTree b -> Node -> Node -> Path
msPath t a b = joinPaths (map fst (getLPath a t)) (map fst (getLPath b t))
            
joinPaths :: Path -> Path -> Path 
joinPaths p q = joinAt (head p) p q

joinAt :: Node -> Path -> Path -> Path
joinAt x (v:vs) (w:ws) | v==w = joinAt v vs ws
joinAt x p      q             = reverse p++(x:q)


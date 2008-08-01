{- |
Module      :  $Header$
Description :  Generic handling of some data structures
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

abstraction over data-containers (lists, sets, maps...)
-}
module OMDoc.Container
  (
     Container(..)
    ,con_convert
    ,con_map
    ,processSubContents
    ,pSCStrip
  )
  where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

-- | Container-Class
class Container a b | a -> b where
  getItems::a->[b]
  fromItems::[b]->a

-- | Container-Conversion
con_convert::(Container q i, Container r i)=>q->r
con_convert c = fromItems (getItems c)

-- | Container-Mapping
con_map::(Container q i, Container r j)=>(i->j)->q->r
con_map f = fromItems . (map f) . getItems

-- Lists are containers
instance Container [a] a where
  getItems = id
  fromItems = id

-- Sets are containers
instance (Ord a)=>Container (Set.Set a) a where
  getItems = Set.toList
  fromItems = Set.fromList

-- Maps are containers
instance (Ord a)=>Container (Map.Map a b) (a,b) where
  getItems = Map.toList
  fromItems = Map.fromList

-- Relations are containers
instance (Ord a)=>Container (Rel.Rel a) (a,a) where
  getItems = Rel.toList
  fromItems = Rel.fromList

-- | use this function to process containers that are stored in other containers
--  - think map key->container - and return container with containers of processed
-- items. the trick is that the key association is the same as long as the
-- processing function does not alter the key (but it may do so)
-- the processing function needs to take an initial status and the final status
-- will be returned
processSubContents::
  (Ord k, Container a (k, p), Container p q
   , Container t r, Container b (k, t) )=>
   (s->[(k, q)]->([(k, r)], s))->s->a->(b, s)
processSubContents
  subprocess
  startvalue
  container =
  let
    allitems = getItems container
    tagged = concatMap (\(k,c) -> map (\i -> (k,i)) (getItems c)) allitems
    (processeditems, finalstatus) = subprocess startvalue tagged
    sorted =
      foldl (\sorted' (k,i) -> insertAtKey (k,i) sorted' )
        []
        processeditems
    kconpairs = map (\(k,l) -> (k,fromItems l)) sorted
  in
    (fromItems kconpairs, finalstatus)
  where
  insertAtKey::(Eq k)=>(k,v)->[(k,[v])]->[(k,[v])]
  insertAtKey (k,v) [] = [(k,[v])]
  insertAtKey (k,v) ((lk,l):r) =
    if k == lk then (lk,v:l):r else (lk,l):(insertAtKey (k,v) r)

-- strip-function for using processSubContents
pSCStrip::(a->b)->(z,a)->b
pSCStrip f (_,a) = f a

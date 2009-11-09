{- |
Module      :  $Header$
Description :  support for partial orders
Copyright   :  (c) Keith Wansbrough 200 and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Support for partial orders

-}

module Common.Partial where

-- | the partial order relation type
type POrder a = a -> a -> Maybe Ordering

-- Ord a implies a total order
totalOrder :: Ord a => POrder a
totalOrder x = Just . compare x

-- | split a list of elements into equivalence classes
equivBy :: POrder a -> [a] -> [[a]]
equivBy order l = equiv0 [] l
  where equiv0 = foldl add
        add cs x = case cs of
          [] -> [[x]]
          [] : _ -> error "Partial.equivBy"
          c@(y : _) : r -> case order x y of
            Just EQ -> (x : c) : r
            _ -> c : add r x

-- | split a set into the minimal elements and the remaining elements
minimalBy :: POrder a -> [a] -> ([a],[a])
minimalBy order es = go es [] []
  where go (x:xs) ms rs = if any (\ e -> order x e == Just GT) es
                          then go xs ms (x:rs)
                          else go xs (x:ms) rs
        go []     ms rs = (reverse ms, reverse rs)

-- | split a set into ranks of elements, minimal first
rankBy :: POrder a -> [a] -> [[a]]
rankBy order l = case l of
    [] -> []
    _ -> let (xs,ys) = minimalBy order l
         in xs : rankBy order ys

-- | A partial-ordering class.
class Partial a where
  pCmp :: POrder a
  pCmp a b = if a <=? b then
                  if b <=? a then Just EQ else Just LT
              else if b <=? a then Just GT else Nothing
  (<=?) :: a -> a -> Bool
  a <=? b = case pCmp a b of
              Just o -> o <= EQ
              _ -> False

equiv :: Partial a => [a] -> [[a]]
equiv = equivBy pCmp

minimal :: Partial a => [a] -> ([a],[a])
minimal = minimalBy pCmp

rank :: Partial a => [a] -> [[a]]
rank = rankBy pCmp

{- undecidable
instance Ord a => Partial a where
  pCmp = totalOrder
-}

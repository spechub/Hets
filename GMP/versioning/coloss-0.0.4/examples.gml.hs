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
-- examples for graded logic. To run these examples,
-- try both provable and sat(isfiable) from the (imported) module
-- Generic on the formulas defined here.

-- quickstart: [ghci|hugs] examples.gml.hs
-- then try ``provable phi1''

import Generic
-- gdiam n phi is the GML formula <>_n phi
gdiam :: Int -> L G -> L G; gdiam k x = box (G k) x

-- gbox n phi is the GML formula []_n phi
gbox :: Int -> L G -> L G; gbox k x = neg (gdiam k (neg x))

-- shorthands for propositional atoms
p0 :: L G; p0  = Atom 0
p1 :: L G; p1  = Atom 1
p2 :: L G; p2  = Atom 2
p3 :: L G; p3  = Atom 3


-- gexcl n phi is the GML formula <>!_n phi
-- so that x |= <>!_n phi if x has exactly n successors that satisfy phi
gexcl :: Int -> L G -> L G;
gexcl 0 x = neg $ gdiam 0  x
gexcl k x = (gdiam (k - 1) x) /\ (neg (gdiam k x))

-- example formulas for GML
phi1 :: L G; phi1 = gbox 0 T 
phi2 :: L G; phi2 = (gdiam 4 p0) --> (gdiam 3 p1)
phi3 :: L G; phi3 = (gdiam (3 + 5) (p1) --> (gdiam 3 p0) \/ (gdiam 5 p1) )
phi4 :: L G; phi4 = neg ( (gdiam 2 p0) /\ (gbox 1 (neg p1)) /\ (gbox 1 (p1)))
phi5 :: L G; phi5 = ((neg p0) /\ (gexcl 2 T) /\ (gexcl 2 p0)) --> (gbox 0 p0)
phi6 :: L G; phi6 = (g2 12) --> gdiam 2 ((gbox 1 p0) --> gdiam 1 p0)

-- the formulas g3 n k are instances of the G3 axiom schema for GML
g3 :: Int -> Int -> (L G)
g3  n1 n2 = (gexcl 0 (p0/\p1))
  -->(((gexcl n1 p0)/\(gexcl n2 p1))
  -->(gexcl (n1 + n2) (p0 \/ p1)))
-- the formulas g2 n are instances of the G2 axiom schema for GML
g2 :: Int -> L G; 
g2 n = gbox 0 (p0 --> p1) --> (gdiam n p0 --> gdiam n p1)

main = putStr $ show $ provable phi5

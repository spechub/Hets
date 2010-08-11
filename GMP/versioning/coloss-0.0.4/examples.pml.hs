{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
-- examples for probabilistic modal logic. To run these examples,
-- try both provable and sat(isfiable) from the (imported) module
-- Generic on the formulas defined here.

-- quickstart: [ghci|hugs] examples.gml.hs
-- then try ``provable phi1''

import Generic

-- pdiam q phi is the PML formula L_p phi
pdiam :: Rational -> L P -> L P; pdiam k x = box (P k) x

-- shorthands for propositional atoms
p0 :: L P; p0  = Atom 0
p1 :: L P; p1  = Atom 1
p2 :: L P; p2  = Atom 2
p3 :: L P; p3  = Atom 3

phi1 :: L P; phi1 = ((pdiam 0.5 ((pdiam 1 (p0 /\ (neg p1)) ) )) /\
  (pdiam 0.5 (pdiam 1 (p3 /\ p2)))) --> ((pdiam 1 (pdiam 1 (p0 \/ p3))))

phi2 :: L P; phi2 = pdiam 0.5 (p0 \/ p3)
phi3 :: L P; phi3 = (pdiam 0.5 phi2) \/ (pdiam 0.5 (neg phi2))
phi4 :: L P; phi4 = (pdiam 0.5 p0) \/ (pdiam 0.5 (neg p0))

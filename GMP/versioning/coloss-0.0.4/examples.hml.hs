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
-- examples for Hennessy-Milner logic. To run these examples,
-- try both provable and sat(isfiable) from the (imported) module
-- Generic on the formulas defined here.

-- quickstart: [ghci|hugs] examples.hml.hs
-- then try ``provable phi1''

import Generic

-- abox 'a' phi is the HML formula [a] phi
abox :: Char -> (L HM) -> (L HM)
abox ag phi = M (HM ag) phi
-- adia is the corresponding diamond
adia :: Char -> (L HM) -> (L HM)
adia ag phi = neg (abox ag (neg phi))

-- shorthands for propositional atoms
p0 :: L HM; p0  = Atom 0
p1 :: L HM; p1  = Atom 1
p2 :: L HM; p2  = Atom 2
p3 :: L HM; p3  = Atom 3

-- some formulas of Hennssy-Milner logic
phi0 :: L HM; phi0 = p0 --> (abox 'a' p0)
phi1 :: L HM; phi1 = (p0 /\ (p0 --> (abox 'a' p0))) --> (abox 'a' p0)
phi2 :: L HM; phi2 = ((abox 'a' p0) \/ (abox 'b' p1)) -->  (adia 'b' p0) \/ (adia 'a' p1)
phi3 :: L HM; phi3 = phi2 --> (abox 'd' phi1)
phi4 :: L HM; phi4 = abox 'c' (phi2 --> (abox 'd' phi1))


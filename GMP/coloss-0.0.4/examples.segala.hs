-- examples for Segala Systems. To run these examples,
-- one needs to run ``gen (flatten seg)'' from examples.gluings.hs
-- try both provable and sat(isfiable) from the (imported) module
-- MySat (generated as above) on the formulas defined here.

-- quickstart: 
--   hugs examples.gluings.hs
--   gen (flatten seg)   <-- generates MySat.hs; leave hugs
--   hugs -98 examples.segala.hs
--   and try provable and satisfiable on the formulas below.

import MySat
import Ratio

-- box 'a' phi is the HML-formula [a] phi
box :: Char -> L1 -> L0; box c phi  = HM0 c phi 

-- dia 'a' phi is the HML-formula <a> phi
dia :: Char -> L1 -> L0; dia c phi = neg (HM0 c (neg phi)) 

-- l p phi is the PML-formula L_p phi
l :: Rational -> L0 -> L1; l r phi = P1 r phi 


-- example from the system description:
phi0 :: L0;  phi0 = box 'i' ( (l (8%10) (dia 'i' (Atom1 0))) --> (l (5%10) (dia 'i' (Atom1 0))) )

-- the two formulas used as example in  Chapter 7.1 of
-- ``Probabilistic Extensions of Process Algebras'' by  Jonsson, Larsen and Yi
-- (as argued in loc.cit., both are satisfiable but not provable)

phi1 :: L0; phi1 = dia 'i'  ((l (7 % 10) (dia 'o' tt)) /\  (l (3 % 10) (dia 'e'  tt))) 
phi2 :: L0; phi2 = dia 'i' (l (9%10) (dia 'o' tt)) 



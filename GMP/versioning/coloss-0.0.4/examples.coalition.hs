-- examples for coalition logic. To run these examples,
-- try both provable and sat(isfiable) from the (imported) module
-- Generic on the formulas defined here.

-- quickstart: [ghci|hugs] examples.coalition.hs
-- then try ``provable phi1''

import Generic

-- cbox [a1, ..., an]  phi is the Coalition formula [{a1, ..., an}]
cbox :: [Int] -> (L C) -> (L C)
cbox ags phi = M (C ags) phi

-- shorthands for propositional atoms
p0 :: L C; p0  = Atom 0
p1 :: L C; p1  = Atom 1
p2 :: L C; p2  = Atom 2
p3 :: L C; p3  = Atom 3


phi0  = (cbox [0, 2, 4] p0) --> (cbox [0] p0)
phi1 = (cbox [0, 2] p0) --> (cbox [0] p0)
phi2 = (cbox [0] p0) --> (cbox [0, 2] p0)
allags :: [Int]; allags = [0..agents]
phi3 = (cbox [0, 1, 7] (phi1 /\ phi2)) --> (cbox allags (phi1 \/ phi2))
phi4 = (cbox [0, 1, 2] (cbox [3, 4, 5] p0)) --> (cbox [0 .. 5] p0)
phi5 = (cbox [1 .. 3] (cbox [3 .. 5] (p1) /\ cbox [1,2] (p2))
                       /\ cbox [4] (cbox [3] (p2) /\ cbox [1,2] (p1)))
    --> cbox [1 .. 5] (cbox [1 .. 5] ((p1) /\ (p2)))


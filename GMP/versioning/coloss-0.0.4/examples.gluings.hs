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
-- Example gluings. To run these examples,
-- try gen (flatten seg) from the (imported) module Combination.
-- this will generate a file ``MySat.hs'' which can be loaded into
-- hugs -98.

-- quickstart: [ghci|hugs] examples.gluings.hs
-- gen (flatten seg)  [--> to generate MySat.hs]
-- hugs -98  examples.segala.hs
-- and try provable and/or satisfiable on the formulas defined there.


import Combination

seg :: Glue; seg = (HM <.> P <.> S);
alt :: Glue; alt = (HM <.> S) <+> (P <.> S);
fu  :: Glue; fu = (K <.> S) <*> (KD <.> S);

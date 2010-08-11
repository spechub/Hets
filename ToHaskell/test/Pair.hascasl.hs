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
{-

types:
A__a :: (*, data)
A__b :: (*, data)
Pair :: (*, data)

values:
f :: (A__a, A__b) -> Pair
g :: Pair -> A__a
A__a :: A__a
A__b :: A__b
Pair :: (A__a, A__b) -> Pair

scope:
Prelude.A__a |-> Prelude.A__a, Type [A__a] []
Prelude.A__a |-> Prelude.A__a, con of A__a
Prelude.A__b |-> Prelude.A__b, Type [A__b] []
Prelude.A__b |-> Prelude.A__b, con of A__b
Prelude.Pair |-> Prelude.Pair, Type [Pair] []
Prelude.Pair |-> Prelude.Pair, con of Pair
Prelude.f |-> Prelude.f, Value
Prelude.g |-> Prelude.g, Value
A__a |-> Prelude.A__a, Type [A__a] []
A__a |-> Prelude.A__a, con of A__a
A__b |-> Prelude.A__b, Type [A__b] []
A__b |-> Prelude.A__b, con of A__b
Pair |-> Prelude.Pair, Type [Pair] []
Pair |-> Prelude.Pair, con of Pair
f |-> Prelude.f, Value
g |-> Prelude.g, Value
-}
module Dummy where
data A__a = A__a
data A__b = A__b
f :: (A__a, A__b) -> Pair
g :: Pair -> A__a
data Pair = Pair !(A__a, A__b)
f (a, b) = Pair (a, b)
g (Pair (a, b)) = a

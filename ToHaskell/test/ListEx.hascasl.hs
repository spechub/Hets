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
List :: (*->*, data)

values:
myhead :: forall a . (List a) -> a
Cons :: forall a . (a, List a) -> List a
Nil :: forall a . List a

scope:
Prelude.Cons |-> Prelude.Cons, con of List
Prelude.List |-> Prelude.List, Type [Cons, Nil] []
Prelude.Nil |-> Prelude.Nil, con of List
Prelude.myhead |-> Prelude.myhead, Value
Cons |-> Prelude.Cons, con of List
List |-> Prelude.List, Type [Cons, Nil] []
Nil |-> Prelude.Nil, con of List
myhead |-> Prelude.myhead, Value
-}
module Dummy where
myhead :: (List a) -> a
myhead (Cons{-a-} (x_11, x_12)) = x_11
data List a = Cons !(a, List a) | Nil

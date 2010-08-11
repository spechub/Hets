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
A__cons :: forall a . a -> (List a) -> List a
A__nil :: forall a . List a

scope:
Prelude.A__cons |-> Prelude.A__cons, con of List
Prelude.A__nil |-> Prelude.A__nil, con of List
Prelude.List |-> Prelude.List, Type [A__cons,
                                     A__nil] []
A__cons |-> Prelude.A__cons, con of List
A__nil |-> Prelude.A__nil, con of List
List |-> Prelude.List, Type [A__cons, A__nil] []
-}
module Dummy where
data List a = A__cons !a !(List a) | A__nil

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

values:
eq :: (Bool, Bool) -> Bool
le :: (Bool, Bool) -> Bool
ne :: (Bool, Bool) -> Bool
neg :: Bool -> Bool
vee :: (Bool, Bool) -> Bool
wedge :: (Bool, Bool) -> Bool

scope:
Prelude.eq |-> Prelude.eq, Value
Prelude.le |-> Prelude.le, Value
Prelude.ne |-> Prelude.ne, Value
Prelude.neg |-> Prelude.neg, Value
Prelude.vee |-> Prelude.vee, Value
Prelude.wedge |-> Prelude.wedge, Value
eq |-> Prelude.eq, Value
le |-> Prelude.le, Value
ne |-> Prelude.ne, Value
neg |-> Prelude.neg, Value
vee |-> Prelude.vee, Value
wedge |-> Prelude.wedge, Value
-}
module Dummy where
eq :: (Bool, Bool) -> Bool
le :: (Bool, Bool) -> Bool
ne :: (Bool, Bool) -> Bool
neg :: Bool -> Bool
vee :: (Bool, Bool) -> Bool
wedge :: (Bool, Bool) -> Bool
neg x
    =
        case x of
            False -> True
            True -> False
wedge (x, y)
    =
        case (x, y) of
            (False, False) -> False
            (True, False) -> False
            (False, True) -> False
            (True, True) -> True
vee (x, y) = neg (wedge (neg x, neg y))
le (x, y) = vee (neg x, y)
eq (x, y) = wedge (le (x, y), le (y, x))
ne (x, y) = wedge (vee (x, y), neg (wedge (x, y)))

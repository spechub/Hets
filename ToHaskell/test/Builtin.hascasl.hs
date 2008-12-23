{-

types:
A__dummy :: (*, data)

values:
p :: A__dummy -> Bool
A__dummy :: A__dummy

scope:
Prelude.A__dummy |-> Prelude.A__dummy, Type [A__dummy] []
Prelude.A__dummy |-> Prelude.A__dummy, con of A__dummy
Prelude.p |-> Prelude.p, Value
A__dummy |-> Prelude.A__dummy, Type [A__dummy] []
A__dummy |-> Prelude.A__dummy, con of A__dummy
p |-> Prelude.p, Value
-}
module Dummy where
data A__dummy = A__dummy
p :: A__dummy -> Bool
p x = True
p x = False
p x
    =
        (\ (a, b, c) -> if b then a else c)
            (p x,
             uncurry{-Bool Bool Bool-} (||)
                 (flip{-Bool Bool Bool-} seq{-Bool Bool-} True (p x),
                  False),
             p x)

module PLpatt.Morphism where

import PLpatt.Sign as Sign

data Morphism = Morphism{ source :: Sigs, target :: Sigs}

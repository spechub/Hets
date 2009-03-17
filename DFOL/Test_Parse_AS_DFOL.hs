{- |
Description :  Test file for Parse_AS_DFOL
-}

import DFOL.AS_DFOL
import DFOL.Parse_AS_DFOL
import Text.ParserCombinators.Parsec
import Common.AnnoState

matrices :: String
matrices = "Nat :: Sort  " ++
           "Mat :: Pi n, m : Nat. Sort  " ++
           "plus :: Pi m, n : Nat; A, B : Mat(n, m). Mat(n, m)  " ++
           ".forall n, m : Int; A, B : Mat(n,m). plus(A, B) == plus(B, A)"

run :: Either ParseError BASIC_SPEC
run = runParser basicSpecP (AnnoState [] ()) "" matrices



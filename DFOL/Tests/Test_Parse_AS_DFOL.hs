{- |
Description :  Test file for Parse_AS_DFOL
-}

import DFOL.AS_DFOL
import DFOL.Parse_AS_DFOL
import Text.ParserCombinators.Parsec
import Common.AnnoState
import Common.Doc
import Common.DocUtils

matrices :: String
matrices = "Nat :: Sort  " ++
           "Mat :: Nat -> Nat -> Sort  " ++
           "plus :: Pi m, n : Nat. Mat(m, n) -> Mat(m, n) -> Mat(m, n)  " ++
           "mult :: Pi p, q, r : Nat. Mat(p, q) -> Mat(q, r) -> Mat(p, r)  " ++
           ".forall m, n : Nat; A, B : Mat(m, n). plus(m, n, A, B) == plus(m, n, B, A) %(plus_commut)%  " ++
           ".forall m, n : Nat; A, B, C : Mat(m, n). plus(m, n, plus(m, n, A, B), C) == plus(m, n, A, plus(m, n, B, C)) %(plus_assoc)%  " {-++
           ".forall p, q, r, s : Nat; A : Mat(p, q); B : Mat(q, r); C : Mat(r, s). mult(p, r, s, mult(p, q, r, A, B), C) == mult(p, q, s, A, mult(q, r, s, B, C)) %(mult_commut)%" -}

run :: Either ParseError BASIC_SPEC
run = runParser basicSpec (AnnoState [] ()) "" matrices

result :: Pretty a => Either ParseError a ->  Doc
result (Right x) = pretty x
result (Left _) = text "Error"

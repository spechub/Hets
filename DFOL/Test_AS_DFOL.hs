{- |
Description :  Test file for AS_DFOL
-}

import DFOL.AS_DFOL
import Common.Id
import Common.AS_Annotation

natTok, matTok, mTok, nTok, aTok, bTok, plusTok :: NAME 

natTok = Token "Nat" $ Range [] 
matTok = Token "Mat" $ Range []
mTok = Token "m" $ Range []
nTok = Token "n" $ Range []
aTok = Token "A" $ Range []
bTok = Token "B" $ Range []
plusTok = Token "+" $ Range []

nat, mat, m, n, a, b, plus :: TERM

nat = Identifier natTok 
mat = Identifier matTok
m = Identifier mTok
n = Identifier nTok
a = Identifier aTok
b = Identifier bTok
plus = Identifier plusTok

decl :: [([NAME], TYPE)]
decl = [([mTok, nTok], Univ nat), 
        ([aTok, bTok], Univ $ Appl mat [m, n])]	

commut :: FORMULA
commut = Forall decl $ Equality (Appl plus [a, b]) (Appl plus [b, a])

spec :: BASIC_SPEC
spec = Basic_spec [Annoted (Decl [natTok] Sort) (Range []) [] [],
                   Annoted (Decl [matTok] $ Pi (take 2 decl) Sort) (Range []) [] [],
                   Annoted (Decl [plusTok] $ Pi decl $ Univ $ Appl mat [m, n]) (Range []) [] [],
                   Annoted (Axiom commut) (Range []) [] []]

     

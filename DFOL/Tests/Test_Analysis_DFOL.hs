{- |
Description :  Test file for Analysis_DFOL
-}

import DFOL.AS_DFOL
import DFOL.Analysis_DFOL
import DFOL.Sign
import Common.Id
import qualified Data.Set as Set

natTok, matTok, mTok, nTok, aTok, bTok, cTok, multTok, pTok, qTok, rTok, sTok :: NAME

natTok = Token "Nat" $ Range []
matTok = Token "Mat" $ Range []
aTok = Token "A" $ Range []
bTok = Token "B" $ Range []
cTok = Token "C" $ Range []
pTok = Token "p" $ Range []
qTok = Token "q" $ Range []
rTok = Token "r" $ Range []
sTok = Token "s" $ Range []
mTok = Token "m" $ Range []
nTok = Token "n" $ Range []
multTok = Token "+" $ Range []

nat, mat, m, n, a, b, c, mult, p, q, r, s :: TERM

nat = Identifier natTok
mat = Identifier matTok
mult = Identifier multTok
a = Identifier aTok
b = Identifier bTok
c = Identifier cTok
m = Identifier mTok
n = Identifier nTok
p = Identifier pTok
q = Identifier qTok
r = Identifier rTok
s = Identifier sTok

sig :: Sign
sig = Sign [([natTok], Sort),
            ([matTok], Func [Univ nat, Univ nat, Sort]),
            ([multTok], Pi [([pTok, qTok, rTok], Univ nat)] $ Func [Univ $ Appl mat [p, q], Univ $ Appl mat [q, r], Univ $ Appl mat [p, r]])]

cont :: CONTEXT
cont = Context [([pTok, qTok, rTok, sTok], Univ nat), ([aTok], Univ $ Appl mat [p, q]), ([bTok], Univ $ Appl mat [q, r]), ([cTok], Univ $ Appl mat [r, s])]

formula :: FORMULA
formula = Forall [([pTok, qTok, rTok, sTok], Univ nat), ([aTok], Univ $ Appl mat [p, q]), ([bTok], Univ $ Appl mat [q, r]), ([cTok], Univ $ Appl mat [r, s])] $ Equality (Appl mult [p, r, s, Appl mult [p, q, r, a, b], c]) (Appl mult [p, q, s, a, Appl mult [q, r, s, b, c]]) 

t :: TYPE
t = alphaRename (Pi [([pTok, qTok, rTok], Univ nat)] $ Func [Univ $ Appl mat [p, q], Univ $ Appl mat [q, r], Univ $ Appl mat [p, r]])
                sig cont

vars :: [NAME]
vars = Set.toList $ getVarsInType t

varsRenames :: [(NAME,NAME)]
varsRenames = renameVars vars $ Set.union (getSymbols sig) (getVars cont)

res :: DIAGN Bool
res = isValidFormula formula sig emptyContext



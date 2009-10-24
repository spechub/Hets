{- |
Description :  Test file for Analysis_DFOL
-}

import DFOL.AS_DFOL
import DFOL.Analysis_DFOL
import DFOL.Sign
import Common.Id
import Data.Maybe
import Common.DocUtils
import qualified Common.Result as Result

mkTok :: String -> Token
mkTok s = Token s nullRange

natTok, matTok, plusTok, mTok, nTok, m1Tok :: NAME
natTok = mkTok "Nat"
matTok = mkTok "Mat"
plusTok = mkTok "plus"
mTok = mkTok "m"
m1Tok = mkTok "m0"
nTok = mkTok "n"

nat, mat, plus, m, n, m1 :: TERM

nat = Identifier natTok
mat = Identifier matTok
plus = Identifier plusTok
m = Identifier mTok
n = Identifier nTok
m1 = Identifier m1Tok

sig :: Sign
sig = Sign [([natTok], Sort),
            ([matTok], Func [Univ nat, Univ nat] Sort),
            ([plusTok], Pi [([mTok, m1Tok], Univ nat)] $ Func [Univ $ Appl mat [m, m1], Univ $ Appl mat [m, m1]] $ Univ $ Appl mat [m, m1])]

cont :: CONTEXT
cont = Context [([mTok, nTok], Univ nat)]

t0, t1, t2, t3, t4 :: TYPE
t0 = Pi [([mTok, nTok], Univ nat)] $ Func [Univ $ Appl mat [m, n], Univ $ Appl mat [m, n]] $ Univ $ Appl mat [m, n]
t1 = Pi [([mTok, m1Tok], Univ nat)] $ Func [Univ $ Appl mat [m, m1], Univ $ Appl mat [m, m1]] $ Univ $ Appl mat [m, m1]
t2 = Func [] $ piRecForm t0
t3 = Func [Univ nat, Univ nat] Sort
t4 = Func [Univ nat] $ Func [Univ nat] $ Func [] Sort




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
m1Tok = mkTok "m1"
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

term :: TERM
term = plus

res :: Result.Result TYPE
res = getType term sig cont

Result.Result _ (Just t) = res


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
import qualified Data.Map as Map
import qualified Data.Set as Set

mkTok :: String -> Token
mkTok s = Token s nullRange

natTok, matTok, plusTok, mTok, nTok, m1Tok :: NAME
natTok = mkTok "Nat"
matTok = mkTok "Mat"
plusTok = mkTok "plus"
mTok = mkTok "m"
m1Tok = mkTok "m0"
nTok = mkTok "n"
xTok = mkTok "x"
x1Tok = mkTok "x1"
x10Tok = mkTok "x10"

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
t2 = Func [] $ typeRecForm t0
t3 = Func [Univ nat, Univ nat] Sort
t4 = Func [Univ nat] $ Func [Univ nat] $ Func [] Sort
t5 = Pi [([xTok],Sort)] $ Pi [([nTok],Sort)] $ Univ $ Appl mat [Identifier xTok, Identifier nTok]
t6 = Pi [([mTok],Sort)] $ Pi [([xTok],Sort)] $ Univ $ Appl mat [Identifier mTok, Identifier xTok]

t :: TYPE
t = let (Pi [([n1],t1)] s1) = t5
        (Pi [([n2],t2)] s2) = t6
        syms1 = Set.delete n1 $ getFreeVars s1
        syms2 = Set.delete n2 $ getFreeVars s2
        v = getNewName n1 $ Set.union syms1 syms2
        type1 = translate (Map.singleton n1 (Identifier v)) syms1 s1
        type2 = translate (Map.singleton n2 (Identifier v)) syms2 s2
        in type2

u :: NAME
u = let (Pi [([n1],t1)] s1) = t5
        (Pi [([n2],t2)] s2) = t6
        syms1 = Set.delete n1 $ getFreeVars s1
        syms2 = Set.delete n2 $ getFreeVars s2
        v = getNewName n1 $ Set.union syms1 syms2
        type1 = translate (Map.singleton n1 (Identifier v)) syms1 s1
        type2 = translate (Map.singleton n2 (Identifier v)) syms2 s2
        in v

{- |
Module      :  $Header$
Description :  Fot testing purpose with GHCI
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
{- SoftFOL.DFGParser must export term,
   Search.SPASS.DB must not have Main as module name
-}
module SPASS.InterActiveTesting where

import Search.SPASS.DB
import Search.Common.Data
import Search.Common.BooleanRing
import Search.Common.Normalization
import Search.SPASS.FormulaWrapper
import Search.SPASS.UnWrap hiding (f1,f2)
import SoftFOL.Sign
import SoftFOL.DFGParser (term)
import Text.ParserCombinators.Parsec

test = "/home/immanuel/dfg/query-files/test.dfg"
tmp = "/home/immanuel/dfg/query-files/tmp.dfg"
tmp2 = "/home/immanuel/dfg/query-files/tmp2.dfg"
alg1 = "/home/immanuel/dfg/query-files/alg_1__t9_alg_1.dfg"
aff1 = "/home/immanuel/dfg/query-files/aff_1__t10_aff_1.dfg"

runOn normalizer file = 
    do (t,_,_):_ <- readDFGFormulae file
       return (normalizer $ wrapTerm t)

elemQ (Binder _ _ f) = elemQ f
elemQ f = f

runTest file = do fs <- readDFGFormulae file
                  mapM_ showAnalyse fs
                  --showAnalyse (fs!!0)
                  --return (map analyse fs)

analyse (t,n,r) = (normalize f,alphaNormalize $ annotateScope f,n::Int,r::Role)
    where f = wrapTerm t

showAnalyse :: (SoftFOL.Sign.SPTerm, Int, Role) -> IO ()
showAnalyse (t,n,r) =
    let (nf,af,n,r) = analyse (t,n,r)
    in do putStrLn "8<------------------------------------------"
          -- putStrLn ("line: " ++ show n) -- ++ "  role: " ++ show r)
          putStrLn (show nf)
          putStrLn (show af)

f1 = "forall([a,b],and(a,or(b,not(a))))"
f2 = "implies(P(A),implies(R(B,A),Q(B)))"
f3 = "forall([A],implies(P(A),forall([B],implies(R(B,A),Q(B)))))"
f4 = "implies(f1(A),implies(f2(B,A),and(f3(B),and(f4(B),f5(B)))))"

br str = getTerm str >>= return . brForm
{-
*SPASS.InterActiveTesting> br "implies(a,b)"
(xor "a" (and "b" "a") true)
-}

getTerm str = run term str >>= return . wrapTerm
getBTerm str = run term str >>= return . fromAlgebra . wrapTerm
reduceBTerm str = run term str >>= return . reduce . fromAlgebra . wrapTerm

getArgs (Var _ args) = args
getArgs (Const _ args) = args

run p input = case (parse p "" input)
              of Left err -> error (show err)
                 Right result  -> return result
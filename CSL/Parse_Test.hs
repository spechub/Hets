{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
import CSL.Sign
import CSL.Analysis         
import CSL.AS_BASIC_CSL
import CSL.Morphism    
import CSL.Tools
import CSL.Reduce_Interface
import CSL.ReduceProve
import CSL.Keywords
import CSL.Parse_AS_Basic
import Common.GlobalAnnotations
import Text.ParserCombinators.Parsec
import Common.AnnoState
import Common.Id
import CSL.Symbol
import Common.AS_Annotation
import Common.Utils (getEnvDef)
import System.IO
import System.Process

-- expression parser

-----------------------------------------------------------------------------
--------------------------------- Parsing -----------------------------------
-----------------------------------------------------------------------------

res1 = runParser expression (emptyAnnos ()) "" "x+y+y"
res2 = runParser expression (emptyAnnos ()) "" "x+y*y"
res3 = runParser expression (emptyAnnos ()) "" "x*y**y"
res4 = runParser expression (emptyAnnos ()) "" "x**y*y"

-- parser for commands without annotations
res6 = runParser command (emptyAnnos ()) "" "solve(x^2=1,x)"
res7 = runParser command (emptyAnnos ()) "" "solve(a*log(sin(x+3))^5 - b, sin(x+3))"
res8 = runParser command (emptyAnnos ()) "" "solve({x+3y=7,y-x=1},{x,y})"
res9 = runParser command (emptyAnnos ()) "" "simplify((x+y)*(x+y+z))"
res10 = runParser command (emptyAnnos ()) "" "remainder(2*x+y,2)"
res11 = runParser command (emptyAnnos ()) "" "remainder((x+y)*(x+2*y),x+3*y)"
res12 = runParser command (emptyAnnos ()) "" "gcd(f(x)+g(x)-l1-l2,f(x)-l1)"
res13 = runParser command (emptyAnnos ()) "" "int(log(x),x)"
res14 = runParser command (emptyAnnos ()) "" "qelim(all(x, ex(y, x2+xy+b>0 and x+ay2+b<=0)))"

res15 = runParser aFormula (emptyAnnos ()) "" "true"
res16 = runParser aFormula (emptyAnnos ()) "" "false"
res17 = runParser aFormula (emptyAnnos ()) "" "2<=3"
res18 = runParser aFormula (emptyAnnos ()) "" "2<3"
res19 = runParser aFormula (emptyAnnos ()) "" "2<3 and 2<=3"
res20 = runParser aFormula (emptyAnnos ()) "" "2<3 or true and false"

-- the basic parser
res21 = runParser parseBasicItems (emptyAnnos ()) "" "operator f,h"
res22 = runParser parseBasicItems (emptyAnnos ()) "" ". solve(x^2=1,x)"

res23 = runParser parseOpDecl (emptyAnnos ()) "" "operator f,h"
res24 = runParser parseAxItems (emptyAnnos ()) "" ". solve(x^2=1,x)"

res25 = runParser basicSpec (emptyAnnos ()) "" "operator f,h . solve(x^2=1,x)"


res30 = runParser extparam () "" "I=0"
res31 = runParser extparam () "" "I < I+1"

res32 = runParser command (emptyAnnos ()) "" "d_4 := 4.0"

res32pure = case res32 of Right a -> a
-- processCmds [(makeNamed "as" res32pure)]

-- declares an equation and ask for the result
castest = do
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  (inp, out, _, _) <- connectCAS reducecmd
  putStrLn "Send the command "
  casDeclareEquation (inp,out) res32pure
  procCmd (inp, out) (makeNamed "test" (Cmd "ask" [(Var (mkSimpleId "d_4"))]))
  -- putStrLn "query term.. "
  -- hPutStrLn inp "d_4;"
  -- res <- getNextResultOutput out
  -- putStrLn ( "Output is " ++ res)
  disconnectCAS (inp, out)
  return ()

-----------------------------------------------------------------------------
------------------------- test of static analysis... ------------------------
-----------------------------------------------------------------------------

testspec = 
    case runParser basicSpec (emptyAnnos ()) "" "operator f,h . solve(x^2=1,x) . solve(x*x=1,x)" of
      Right a -> a

res26 = splitSpec testspec emptySig

res27 = basicCSLAnalysis (testspec, emptySig, [])

-----------------------------------------------------------------------------
--------------------------------- Analysis ----------------------------------
-----------------------------------------------------------------------------

-- getAtomsFromFile fp = readFile fp >>= return . getAtomsFrom

-- getAtomsFrom s = 
--     case runParser basicSpec (emptyAnnos ()) "" s of
--       Right a -> map (\ (x:l) -> (x, 1 + length l)) $ group $ sort $ getBSAtoms a
--       _ -> error "no parse"


-----------------------------------------------------------------------------
--------------------------------- Morphisms ---------------------------------
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
--------------------------------- Signature ---------------------------------
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
------------------------------ CSL Interface -----------------------------
-----------------------------------------------------------------------------
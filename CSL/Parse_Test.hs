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
import CSL.Symbol
import Common.AS_Annotation
import Common.Utils (getEnvDef)
import System.IO
import System.Process

-- expression parser

-----------------------------------------------------------------------------
--------------------------------- Parsing -----------------------------------
-----------------------------------------------------------------------------

res1 = runParser expression 2 "" "x+y+y"
res2 = runParser expression 2 "" "x+y*y"
res3 = runParser expression 2 "" "x*y**y"
res4 = runParser expression 2 "" "x**y*y"

-- parser for commands without annotations
res6 = runParser command 2 "" "solve(x^2=1,x)"
res7 = runParser command 2 "" "solve(a*log(sin(x+3))^5 - b, sin(x+3))"
res8 = runParser command 2 "" "solve({x+3y=7,y-x=1},{x,y})"
res9 = runParser command 2 "" "simplify((x+y)*(x+y+z))"
res10 = runParser command 2 "" "remainder(2*x+y,2)"
res11 = runParser command 2 "" "remainder((x+y)*(x+2*y),x+3*y)"
res12 = runParser command 2 "" "gcd(f(x)+g(x)-l1-l2,f(x)-l1)"
res13 = runParser command 2 "" "int(log(x),x)"
res14 = runParser command 2 "" "qelim(all(x, ex(y, x2+xy+b>0 and x+ay2+b<=0)))"

res15 = runParser aFormula 2 "" "true"
res16 = runParser aFormula 2 "" "false"
res17 = runParser aFormula 2 "" "2<=3"
res18 = runParser aFormula 2 "" "2<3"
res19 = runParser aFormula 2 "" "2<3 and 2<=3"
res20 = runParser aFormula 2 "" "2<3 or true and false"

-- the basic parser
res21 = runParser parseBasicItems (emptyAnnos ()) "" "operator f,h"
res22 = runParser parseBasicItems (emptyAnnos ()) "" ". solve(x^2=1,x)"

res23 = runParser parseOpDecl (emptyAnnos ()) "" "operator f,h"
res24 = runParser parseAxItems (emptyAnnos ()) "" ". solve(x^2=1,x)"

res25 = runParser basicSpec (emptyAnnos ()) "" "operator f,h . solve(x^2=1,x)"


res30 = runParser extparam () "" "I=0"
res31 = runParser extparam () "" "I < I+1"

res32 = runParser command 2 "" "d_4 := 4.0"

res32pure = case res32 of Right a -> a
-- processCmds [(makeNamed "as" res32pure)]

-- declares an equation and ask for the result
castest = do
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  (inp, out, _, _) <- connectCAS reducecmd
  putStrLn "Send the command "
  casDeclareEquation (inp,out) res32pure
  putStrLn "query term.. "
  hPutStrLn inp "d_4;"
  res <- getNextResultOutput out
  putStrLn ( "Output is " ++ res)
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
--------------------------------- Morphisms ---------------------------------
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
--------------------------------- Signature ---------------------------------
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
------------------------------ CSL Interface -----------------------------
-----------------------------------------------------------------------------
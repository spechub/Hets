-- expression parser

runParser expression 2 "" "x+y+y"
runParser expression 2 "" "x+y*y"
runParser expression 2 "" "x*y**y"
runParser expression 2 "" "x**y*y"

-- parser for operators

runParser operatordecl 2 "operator f,g, linear"

-- parser for commands without annotations
runParser command 2 "" "solve(x^2=1,x)"
runParser command 2 "" "solve(a*log(sin(x+3))^5 - b, sin(x+3))"
runParser command 2 "" "solve({x+3y=7,y-x=1},{x,y})"
runParser command 2 "" "simplify((x+y)*(x+y+z))"
runParser command 2 "" "remainder(2*x+y,2)"
runParser command 2 "" "remainder((x+y)*(x+2*y),x+3*y)"
runParser command 2 "" "gcd(f(x)+g(x)-l1-l2,f(x)-l1)"
runParser command 2 "" "int(log(x),x)"
runParser command 2 "" "qelim(all(x, ex(y, x2+xy+b>0 and x+ay2+b<=0)))"

runParser aFormula 2 "" "true"
runParser aFormula 2 "" "false"
runParser aFormula 2 "" "2<=3"
runParser aFormula 2 "" "2<3"
runParser aFormula 2 "" "2<3 and 2<=3"
runParser aFormula 2 "" "2<3 or true and false"

-- the basic parser
runParser parseBasicItems (AnnoState.emptyAnnos ()) "" "operator f,h"
runParser parseBasicItems (AnnoState.emptyAnnos ()) "" ". solve(x^2=1,x)"

runParser parseOpDecl (AnnoState.emptyAnnos ()) "" "operator f,h"
runParser parseAxItems (AnnoState.emptyAnnos ()) "" ". solve(x^2=1,x)"

-- das hier geht nicht
runParser basicSpec (AnnoState.emptyAnnos ()) "" "operator f,h"



-- beispiele für propositional
runParser basicSpec (AnnoState.emptyAnnos ()) "" "props a,b"
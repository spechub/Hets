module RunMixfixParser where

import MixfixParser
import PrettyPrint
import Print_AS_Basic
import GlobalAnnotationsFunctions
import Set

import Token
import Formula
import Anno_Parser

-- start testing

testForm l r t = 
    let g = addGlobalAnnos emptyGlobalAnnos 
			 $ map (parseString annotationL) l
	in printText0 g $
	   resolveFormula g (mkSet $ map (parseString parseId) r)
		      emptySet (parseString formula t)

myAnnos = [ "%prec({__+__} < {__*__})%", "%prec({__*__} < {__^__})%"
	  , "%left_assoc(__+__)%"
	  , "%list([__], [], __::__)%"]

myIs = ["__^__", "__*__", "__+__", "[__]", "____p", "q____","____x____",
        "{____}","__-__",
	"x", "0", "1", "2", "3", "4", "5", "a", "b", "-__", "__!"]

polynom = "4*x^4+3*x^3+2*x^2+1*x^1+0*x^0=0"

testAppl t = testForm myAnnos myIs t 

module RunMixfixParser where

import MixfixParser
import AS_Basic_CASL
import GlobalAnnotations
import GlobalAnnotationsFunctions
import ParsecPrim(Parser)
import Set
import Id
import Result

import Token
import Formula
import Anno_Parser

-- start testing
stdAnnosL, stdOpsL, stdPredsL :: [String]
stdAnnosL = [ "%prec {__+__} < {__*__}\n" 
	  , "%prec {__*__} < {__^__}\n"
          , "%prec {+__} <> {__ ^ __}\n"
          , "%string [], __::__\n"
	  , "%left_assoc(__+__,__*__)%"
	  , "%number __@@__\n"
          , "%floating __:::__, __E__\n"
	  , "%list([__], [], __::__)%"]

mkAnnos :: [String] -> GlobalAnnos
mkAnnos l = addGlobalAnnos emptyGlobalAnnos 
			 $ map (parseString annotationL) l

stdAnnos :: GlobalAnnos
stdAnnos = mkAnnos stdAnnosL

stdOpsL = ["__^__", "__*__", "__+__", "[__]", "____p", "q____","____x____",
        "{____}","__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
	"x", "0", "1", "2", "3", "4", "5", "a", "b", "-__", "__!"]

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
	     "__/=__", "even__", "odd__", "__isEmpty"] 

mkIds :: [String] -> Set Id
mkIds = mkSet . map (parseString parseId)

stdOps, stdPreds :: Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL 

resolveForm :: Parser (Result FORMULA)
resolveForm = 
      resolveFormula stdAnnos stdOps stdPreds `fmap` formula

resolveTerm :: Parser (Result TERM)
resolveTerm = 
      resolveMixfix stdAnnos stdOps stdPreds False `fmap` term

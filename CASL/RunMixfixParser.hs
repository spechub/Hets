module CASL.RunMixfixParser where

import Common.AnnoState
import CASL.MixfixParser
import CASL.AS_Basic_CASL
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Lib.Set
import Common.Id
import Common.Result
import Common.Lexer
import Common.Lib.Pretty
import Common.PrettyPrint

import Common.Token
import CASL.Formula
import Common.Anno_Parser
import CASL.ShowMixfix -- (showTerm, showFormula)

-- start testing
stdAnnosL, stdOpsL, stdPredsL :: [String]
stdAnnosL = [ "%prec {__+__} < {__*__}\n" 
	  , "%prec {__*__} < {__^__}\n"
          , "%prec {+__} <> {__ ^ __}\n"
          , "%string empty, __::::__\n"
	  , "%left_assoc(__+__,__*__)%"
	  , "%number __@@__\n"
          , "%floating __:::__, __E__\n"
	  , "%list([__], [], __::__)%"]

mkAnnos :: [String] -> GlobalAnnos
mkAnnos l = addGlobalAnnos emptyGlobalAnnos 
			 $ map (parseString annotationL) l

stdAnnos :: GlobalAnnos
stdAnnos = mkAnnos stdAnnosL

stdOpsL = ["__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__", 
        "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
	"-__", "__!"] ++ 
          [ "____p", "q____","____x____", "{____}",
          "repeat__until__", "while__do__od", 
	    "__where__but__", "__where__done"] ++ 
        map (:[]) 
        "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
         ++ ["A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__", 
	     "a[c,d]", "__a[c,d]__", "A[a]", "A__B", 
	     "A__", "__[a]", "__p", 
	     "__[__]__", "[__]__", "__[__]"] 

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
	     "__/=__", "even__", "odd__", "__isEmpty",
	    "__<=__<=__"] ++ map (:[]) "abcdpqrstuvwxyzPQRSTUVWXYZ" 

mkIds :: [String] -> Set Id
mkIds = fromList . map (parseString parseId)

stdOps, stdPreds :: Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL 

resolveForm :: AParser (Result FORMULA)
resolveForm = 
      resolveFormula stdAnnos stdOps stdPreds `fmap` formula

resolveTerm :: AParser (Result TERM)
resolveTerm = 
      resolveMixfix stdAnnos stdOps stdPreds False `fmap` term

data WrapString = WrapString String
instance Show WrapString where
    showsPrec _ (WrapString s) _ = s 

instance PrettyPrint WrapString where
    printText0 _ (WrapString s) = text s 

testTerm :: AParser WrapString
testTerm = do t <- term
	      return $ WrapString $ showTerm t ""

testTermMix :: AParser WrapString
testTermMix = do Result ds mt <- resolveTerm
		 return $ WrapString $ 
			case mt of Just t -> showTerm t ""
				   _ -> show ds

testFormula :: AParser WrapString
testFormula = do f <- formula
		 return $ WrapString $ showFormula f ""

testFormulaMix :: AParser WrapString
testFormulaMix = do Result ds m <- resolveForm
		    return $ WrapString $ 
			   case m of Just f -> showFormula f ""
				     _ -> show ds

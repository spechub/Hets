{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

  Parser for CoCASL
-}

module CoCASL.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import CoCASL.AS_CoCASL
import Common.Lib.Parsec
import CASL.Formula
import CASL.OpItem
import CASL.Parse_AS_Basic (sigItems)

cocaslFormula :: AParser C_FORMULA
cocaslFormula = 
    do o <- oBracketT
       m <- modality []
       c <- cBracketT
       f <- formula cocasl_reserved_words
       return (Box m f $ toPos o [] c)
    <|> 
    do o <- asKey lessS
       m <- modality [greaterS] -- do not consume matching ">"!
       c <- asKey greaterS
       f <- formula cocasl_reserved_words
       return (Diamond m f $ toPos o [] c)

modality :: [String] -> AParser MODALITY
modality ks = 
    do t <- term (prodS : ks ++ cocasl_reserved_words)
	    -- put the term in parens if you need to use "*"
       ((do asKey prodS; return ()) <|> return ())
	    -- presence of "*" is not stored yet! 
       return $ Term_mod t

instance AParsable C_FORMULA where
  aparser = cocaslFormula


cBasic :: AParser C_BASIC_ITEM
cBasic =  do f <- asKey cofreeS
             ti <- coSigItems 
             return (codatatypeToCofreetype ti (tokPos f))
      <|> do g <- asKey cogeneratedS
	     do t <- sigItems cocasl_reserved_words
		return (CoSort_gen [Annoted t [] [] []] [tokPos g])
	       <|> 
	       do o <- oBraceT
	          is <- annosParser (sigItems cocasl_reserved_words)
	          c <- cBraceT
	          return (CoSort_gen is
		            (toPos g [o] c)) 

coSigItems :: AParser C_SIG_ITEM
coSigItems = itemList cocasl_reserved_words cotypeS codatatype CoDatatype_items

codatatype :: [String] -> AParser CODATATYPE_DECL
codatatype ks = 
    do s <- sortId ks
       addAnnos
       e <- asKey defnS
       addAnnos
       a <- getAnnos
       (Annoted v _ _ b:as, ps) <- acoAlternative ks `separatedBy` barT
       return (CoDatatype_decl s (Annoted v [] a b:as) 
			(map tokPos (e:ps)))

acoAlternative :: [String] -> AParser (Annoted COALTERNATIVE)
acoAlternative ks = 
    do a <- coalternative ks
       an <- annos
       return (Annoted a [] [] an)

coalternative :: [String] -> AParser COALTERNATIVE
coalternative ks = 
    do s <- pluralKeyword sortS
       (ts, cs) <- sortId ks `separatedBy` anComma
       return (CoSubsorts ts (map tokPos (s:cs)))
    <|> 
    do i <- consId ks
       cocomp (Just i)
    <|>
    do cocomp Nothing
    where 
      cocomp i =
       do   o <- oParenT
	    (cs, ps) <- cocomponent ks `separatedBy` anSemi
	    c <- cParenT
	    let qs = toPos o ps c 
            do   q <- quMarkT
		 return (CoPartial_construct i cs (qs++[tokPos q]))
	      <|> return (CoTotal_construct i cs qs)
	 <|> return (CoTotal_construct i [] [])

cocomponent :: [String] -> AParser COCOMPONENTS
cocomponent ks = 
    do (is, cs) <- parseId ks `separatedBy` anComma
       c <- colonST
       t <- opType ks
       let p = map tokPos (cs++[c]) 
       return $ CoSelect is t p

instance AParsable C_SIG_ITEM where
  aparser = coSigItems

instance AParsable C_BASIC_ITEM where
  aparser = cBasic


---- helpers ----------------------------------------------------------------

codatatypeToCofreetype ::  C_SIG_ITEM -> Pos -> C_BASIC_ITEM
codatatypeToCofreetype d pos =
   case d of
     CoDatatype_items ts ps -> CoFree_datatype ts (pos : ps)
     _ -> error "codatatypeToCofreetype"

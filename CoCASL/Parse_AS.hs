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
    <|> 
    do d <- asKey diamondS
       f <- formula cocasl_reserved_words
       let p = tokPos d
       return (Diamond (Simple_mod $ Token emptyS p) f [p])

modality :: [String] -> AParser MODALITY
modality ks = 
    do t <- term (ks ++ cocasl_reserved_words)
       return $ Term_mod t
   <|> return (Simple_mod $ mkSimpleId emptyS)

instance AParsable C_FORMULA where
  aparser = cocaslFormula


cBasic :: AParser C_BASIC_ITEM
cBasic =  do f <- asKey cofreeS
             ti <- cotypeItems ks
             return (codatatypeToCofreetype ti (tokPos f))
      <|> do g <- asKey cogeneratedS
	     do t <- cotypeItems ks
		return (CoSort_gen [Annoted t [] [] []] [tokPos g])
	       <|> 
	       do o <- oBraceT
	          is <- annosParser (sigItems ks)
	          c <- cBraceT
	          return (CoSort_gen is
		            (toPos g [o] c)) 

coSigItems :: AParser C_SIG_ITEM
coSigItems = itemList cocasl_keywords cotypeS codatatype CoDatatype_items

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
    where cocomp i =
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
       (b, t, _) <- opSort ks
       let p = map tokPos (cs++[c]) 
       return $ if b then CoPartial_select is t p
	      else  CoTotal_select is t p

instance AParsable C_SIG_ITEM where
  aparser = coSigItems

instance AParsable C_BASIC_ITEM where
  aparser = cBasic


---- helpers ----------------------------------------------------------------

codatatypeToCofreetype ::  C_SIG_ITEMS -> Pos -> C_BASIC_ITEMS 
codatatypeToCofreetype d pos =
   case d of
     CoDatatype_items ts ps -> CoFree_datatype ts (pos : ps)
     _ -> error "codatatypeToCofreetype"

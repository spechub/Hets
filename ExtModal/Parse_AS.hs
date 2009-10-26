{-
Module      :  ./ExtModal/AS_ExtModal.der.hs
Description :  Parser for extended modal logic
Copyright   :  
License     :  

Maintainer  :  
Stability   :  
Portability :  

-}

module ExtModal.Parse_AS where 



import Data.Char
import Text.ParserCombinators.Parsec

import Common.Id
import Common.Token
import Common.Lexer
import Common.AnnoState
import Common.Keywords
import Common.AS_Annotation

import CASL.Formula
import CASL.OpItem

import ExtModal.AS_ExtModal
import ExtModal.Keywords


ext_modal_reserved_words :: [String]
ext_modal_reserved_words = 
	untilS:sinceS:allPathsS:somePathsS:generallyS:eventuallyS:generallyS:atS:hereS:timeS:nominalS:nominalsS:
	hithertoS:previouslyS:muS:nuS:diamondS:termS:rigidS:flexibleS:modalityS:[modalitiesS]
{-List of reserved words-}



{-Modal formula parser-}

modalFormulaParser :: AParser st EM_FORMULA
modalFormulaParser = 
	{-box, <=-}
	do open <- oBracketT
	   modal <- parseModality
	   close <- cBracketT
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal True (value 10 number) formula $ toRange open [] close)
	<|>
	{-box, >=-}
	do open <- oBracketT
	   modal <- parseModality
	   close <- cBracketT
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal False (value 10 number) formula $ toRange open [] close)
	<|>
	{-diamond, <=-}
	do open <- asKey lessS
	   modal <- parseModality 
	   close <- asKey greaterS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal True (value 10 number) formula $ toRange open [] close)
	<|>
	{-diamond, >=-}
	do open <- asKey lessS
	   modal <- parseModality 
	   close <- asKey greaterS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal False (value 10 number) formula $ toRange open [] close)
	<|>
	{-empty diamond, <=-}
	do diam <- asKey diamondS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos diam
	   return (BoxOrDiamond False (Simple_modality $ Token emptyS pos) True (value 10 number) formula pos)
	<|>
	{-empty diamond, >=-}
	do diam <- asKey diamondS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos diam
	   return (BoxOrDiamond False (Simple_modality $ Token emptyS pos) False (value 10 number) formula pos)
	<|>
	{-Until, U-}
	do formula1 <- primFormula ext_modal_reserved_words
	   unt <- asKey untilS
	   formula2 <- primFormula ext_modal_reserved_words 
	   let pos = tokPos unt
	   return (UntilSince True formula1 formula2 pos)
	<|>	
	{-Since, S-}
	do formula1 <- primFormula ext_modal_reserved_words
	   snc <- asKey sinceS
	   formula2 <- primFormula ext_modal_reserved_words 
	   let pos = tokPos snc
	   return (UntilSince False formula1 formula2 pos)
	<|>
	{-All paths, A-}
	do ap <- asKey allPathsS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos ap
	   return (PathQuantification True formula pos)
	<|>
	{-Some paths, E-}
	do sp <- asKey somePathsS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos sp
	   return (PathQuantification False formula pos)
	<|>
	{-Next, X-}
	do nxt <- asKey nextS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos nxt
	   return (NextY True formula pos)
	<|>
	{-Yesterday, Y-}
	do ysd <- asKey yesterdayS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos ysd
	   return (NextY False formula pos)
	<|>
	{-Generally, G-}
	do grl <- asKey generallyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos grl
	   return (StateQuantification True True formula pos)
	<|>
	{-Eventually, F-}
	do evt <- asKey eventuallyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos evt
	   return (StateQuantification True False formula pos)
	<|>
	{-Hitherto, H-}
	do hth <- asKey hithertoS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos hth
	   return (StateQuantification False True formula pos)
	<|>
	{-Previously, P-}
	do prv <- asKey previouslyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos prv
	   return (StateQuantification False False formula pos)
	<|>
	{-parse Mu-}
	do mu <- asKey muS
	   z <- varId ext_modal_reserved_words
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos mu
	   return (FixedPoint True z formula pos)
	<|>	
	{-parse Nu-}
	do nu <- asKey nuS
	   z <- varId ext_modal_reserved_words
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos nu
	   return (FixedPoint False z formula pos)
	<|>
	{-@-}
	do at <- asKey atS
	   nom <- simpleId
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos at
	   return (Hybrid True (Nominal nom) formula pos)
	<|>
	{-Here-}
	do her <- asKey hereS
	   nom <- simpleId
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos her
	   return (Hybrid False (Nominal nom) formula pos)
	

{-Term modality parser-}
parseModality :: GenParser Char (AnnoState st) MODALITY
parseModality =
	do t <- simpleId
	   return (Simple_modality t)
	<|>
	do opn <- asKey tmOParanthS
	   t <- parseModality 
	   cls <- asKey tmCParanthS
	   return t
	<|>
	do f <- primFormula ext_modal_reserved_words
	   grd <- asKey tmGuardS
	   return (Guard f)
	<|>
	do t <- parseModality 
	   tc <- asKey tmTransClosS
	   return (TransitiveClosure t)
	<|>
	do t1 <- parseModality
	   cmp <- asKey tmCompositionS
	   t2 <- parseModality
	   return (Composition t1 t2)
	<|>
	do t1 <- parseModality
	   un <- asKey tmUnionS
	   t2 <- parseModality
	   return (Union t1 t2)
	<|> return (Simple_modality $ mkSimpleId emptyS)

instance AParsable EM_FORMULA where
	aparser = modalFormulaParser

{-Signature parser-}

rigor :: AParser st RIGOR
rigor = (asKey rigidS >> return Rigid)
	<|> (asKey flexibleS >> return Flexible)

sigItemParser :: AParser st EM_SIG_ITEM
sigItemParser =
	do rig <- rigor
	   do itemList ext_modal_reserved_words opS opItem (Rigid_op_items rig)
	      <|> itemList ext_modal_reserved_words predS predItem (Rigid_pred_items rig)

instance AParsable EM_SIG_ITEM where 
	aparser = sigItemParser
	
{-Basic item parser-}

mKey :: AParser st Token
mKey = asKey modalityS <|> asKey modalitiesS

nKey :: AParser st Token
nKey = asKey nominalS <|> asKey nominalsS

basicItemParser :: AParser st EM_BASIC_ITEM
basicItemParser = 
	do k <- mKey 
	   (annoId, ks) <- separatedBy (annoParser simpleId) anComma
	   parseAxioms False annoId ( catRange $ k : ks )
	<|>
	do tmp <- asKey timeS
	   k <- mKey 
	   (annoId, ks) <- separatedBy (annoParser simpleId) anComma
	   parseAxioms True annoId ( catRange $ k : ks )
	<|>
	do k <- nKey
	   (annoId, ks) <- separatedBy (annoParser simpleId) anComma
	   let pos = catRange $ k : ks
	   return (Nominal_decl annoId pos)

parseAxioms :: Bool -> [Annoted SIMPLE_ID] -> Range -> AParser st EM_BASIC_ITEM
parseAxioms b annoId pos = 
	 do o <- oBraceT
	    (someAxioms, qs) <- annoParser (formula ext_modal_reserved_words)
		  `separatedBy` anSemi
	    c <- cBraceT
	    return (Simple_mod_decl b annoId someAxioms $ pos `appRange` toRange o qs c)
	 <|> do return (Simple_mod_decl b annoId [] pos)
	

instance AParsable EM_BASIC_ITEM where 
	aparser = basicItemParser 

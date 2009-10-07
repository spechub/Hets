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


import Common.AnnoState
import ExtModal.AS_ExtModal

ext_modal_reserved_words :: [String]
ext_modal_reserved_words = 
	untilS:sinceS:allPathS:somePathsS:generallyS:finallyS:generallyS:atS:hereS:timeS:nominalS:nominalsS:
	hithertoS:previouslyS:muS:nuS:diamondS:termS:rigidS:flexibleS:modalityS:[modalitiesS]
{-list of reserved words-}


modalFormulaParse :: AParser st EM_FORMULA
modalFormulaParser = 
	{-box, <=-}
	do open <- oBracketT
	   modal <- {-parse (term) modality-}
	   close <- cBracketT
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-box, >=-}
	do open <- oBracketT
	   modal <- {-parse (term) modality-}
	   close <- cBracketT
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-diamond, <=-}
	do open <- asKey lessS
	   modal <- {-parse (term) modality-}
	   close <- asKey greaterS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-diamond, >=-}
	do open <- asKey lessS
	   modal <- {-parse (term) modality-}
	   close <- asKey greaterS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-empty diamond, <=-}
	do diam <- diamondS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos diam
	   return (BoxOrDiamond False (Simple_mod $ Token emptyS pos) LeqOrGeq True formula pos)
	<|>
	{-empty diamond, >=-}
	do diam <- diamondS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos diam
	   return (BoxOrDiamond False (Simple_mod $ Token emptyS pos) LeqOrGeq False formula pos)
	<|>
	{-Until, U-}
	do formula1 <- primFormula ext_modal_reserved_words
	   unt <- asKey untilS
	   (formula2, sb) <- primFormula ext_modal_reserved_words `separatedBy` (asKey untilS)
	   return $ UntilSince True formula1 formula2 $ catRange $ unt : sb
	<|>	
	{-Since, S-}
	do formula1 <- primFormula ext_modal_reserved_words
	   snc <- asKey sinceS
	   (formula2, sb) <- primFormula ext_modal_reserved_words `separatedBy` (asKey sinceS)
	   return $ UntilSince False formula1 formula2 $ catRange $ snc : sb
	<|>
	{-All paths, A-}
	do ap <- asKey allPathsS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos ap
	   return (PathQuantification True formula pos)
	<|>
	{-Some paths, E-}
	do sp <- asKey somePathsS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos sp
	   return (PathQuantification False formula pos)
	<|>
	{-Next, X-}
	do nxt <- asKey nextS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos nxt
	   return (NextY True formula pos)
	<|>
	{-Yesterday, Y-}
	do ysd <- asKey yesterdayS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos ysd
	   return (NextY False formula pos)
	<|>
	{-Generally, G-}
	do grl <- asKey generallyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos grl
	   return (StateQuantification True True formula pos)
	<|>
	{-Eventually, F-}
	do evt <- asKey eventuallyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos evt
	   return (StateQuantification True False formula pos)
	<|>
	{-Hitherto, H-}
	do hth <- asKey hithertoS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos hth
	   return (StateQuantification False True formula pos)
	<|>
	{-Previously, P-}
	do prv <- asKey previouslyS
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos prv
	   return (StateQuantification False False formula pos)
	<|>
	{-parse Mu-}
	do mu <- asKey muS
	   Z <- {-parse variable-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos mu
	   return (FixedPoint True formula pos)
	<|>	
	{-parse Nu-}
	do nu <- asKey nuS
	   Z <- {-parse variable-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos nu
	   return (FixedPoint False formula pos)
	<|>
	{-@-}
	do at <- asKey atS
	   nom <- {-parse nominal-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos at
	   return (Hybrif True nom formula pos)
	<|>
	{-Here-}
	do her <- asKey hereS
	   nom <- {-parse nominal-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos her
	   return (Hybrif False nom formula pos)
	
	

instance AParsable EM_FORMULA where
	aparser = modalFormulaParser



sigItemParser :: AParser st EM_SIG_ITEM
sigItemParser = {-parse sigItem-}

instance AParsable EM_SIG_ITEM where 
	aparser = sigItemParser
	


basicItemParser :: AParser st EM_BASIC_ITEM
basicItemParser = {-parse basicItem-}

instance AParsable EM_BASIC_ITEM where 
	aparser = basicItemParser 

{-
Module      :  ./ExtModal/AS_ExtModal.der.hs
Description :  Parser for extended modal logic
Copyright   :  
License     :  

Maintainer  :  
Stability   :  
Portability :  

-}

module ExtModal.Parser_AS where 


import Common.AnnoState
import ExtModal.AS_ExtModal

ext_modal_reserved_words :: [String]
ext_modal_reserved_words = 
	untilS:sinceS:allPathS:somePathsS:generallyS:finallyS:generallyS:
	hithertoS:previouslyS:muS:nuS:diamondS:termS:rigidS:flexibleS:modalityS:[modalitiesS]
{-list of reserved words-}


modalFormulaParse :: AParser st EM_FORMULA
modalFormulaParser = 
	{-box, <=-}
	do open <- oBracketT
	   modal <- {-parse (term) modality-}
	   close <- cBracketT
	   grading <- asKey lessEq
	   number <- {- parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-box, >=-}
	do open <- oBracketT
	   modal <- {-parse (term) modality-}
	   close <- cBracketT
	   grading <- asKey greaterEq
	   number <- {- parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-diamond, <=-}
	do open <- asKey lessS
	   modal <- {-parse (term) modality-}
	   close <- asKey greaterS
	   grading <- asKey lessEq
	   number <- {-parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-diamond, >=-}
	do open <- asKey lessS
	   modal <- {-parse (term) modality-}
	   close <- asKey greaterS
	   grading <- asKey greaterEq
	   number <- {-parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-empty diamond, <=-}
	do diam <- diamondS
	   grading <- asKey lessEq
	   number <- {-parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos diam
	   return (BoxOrDiamond False (Simple_mod $ Token emptyS pos) LeqOrGeq True formula pos)
	<|>
	{-empty diamond, >=-}
	do diam <- diamondS
	   grading <- asKey greaterEq
	   number <- {-parse number-}
	   formula <- primFormula ext_modal_reserved_words
	   let pos <- tokPos diam
	   return (BoxOrDiamond False (Simple_mod $ Token emptyS pos) LeqOrGeq False formula pos)
	<|>
	{-Until-}
	do formula1 <- primFormula ext_modal_reserved_words
	   unt <- asKey untilS
	   formula2 <- primFormula ext_modal_reserved_words
	   return (UntilSince True formula1 formula2 $ toRange {-?-} [] {-?-})
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
		{-parse Hybrid operators-}

	

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

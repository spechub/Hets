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
import ExtModal.Keywords

ext_modal_reserved_words :: [String]
ext_modal_reserved_words = 
	untilS:sinceS:allPathS:somePathsS:generallyS:finallyS:generallyS:atS:hereS:timeS:nominalS:nominalsS:
	hithertoS:previouslyS:muS:nuS:diamondS:termS:rigidS:flexibleS:modalityS:[modalitiesS]
{-List of reserved words-}

{-Modal formula parser-}

modalFormulaParse :: AParser st EM_FORMULA
modalFormulaParser = 
	{-box, <=-}
	do open <- oBracketT
	   modal <- parseModality
	   close <- cBracketT
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-box, >=-}
	do open <- oBracketT
	   modal <- parseModality
	   close <- cBracketT
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond True modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-diamond, <=-}
	do open <- asKey lessS
	   modal <- parseModality 
	   close <- asKey greaterS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq True number formula $ toRange open [] close)
	<|>
	{-diamond, >=-}
	do open <- asKey lessS
	   modal <- parseModality 
	   close <- asKey greaterS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   return (BoxOrDiamond False modal LeqOrGeq False number formula $ toRange open [] close)
	<|>
	{-empty diamond, <=-}
	do diam <- asKey diamondS
	   grading <- asKey lessEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos diam
	   return (BoxOrDiamond False (Simple_mod $ Token emptyS pos) LeqOrGeq True formula pos)
	<|>
	{-empty diamond, >=-}
	do diam <- asKey diamondS
	   grading <- asKey greaterEq
	   number <- getNumber
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos diam
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
	   Z <- varId ext_ modal_reserved_words
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos mu
	   return (FixedPoint True Z formula pos)
	<|>	
	{-parse Nu-}
	do nu <- asKey nuS
	   Z <- varId ext_modal_reserved_words
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos nu
	   return (FixedPoint False Z formula pos)
	<|>
	{-@-}
	do at <- asKey atS
	   nom <- simpleId
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos at
	   return (Hybrif True nom formula pos)
	<|>
	{-Here-}
	do her <- asKey hereS
	   nom <- simpleId
	   formula <- primFormula ext_modal_reserved_words
	   let pos = tokPos her
	   return (Hybrif False nom formula pos)
	

{-Term modality parser-}
parseModality :: [String] -> AParser st MODALITY
parseModality =
	do t <- simpleId
	   return (Simple_modality t)
	<|>
	do opn <- asKey tmOParanthS
	   t <- parseModality 
	   cls <- asKey tmCParanthS
	   return t
	<|>
	do f <- modalFormulaParser
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
	   let pos = catRange $ k : ks
	   do o <- oBraceT
	      (someAxioms, qs) <- annoParser (formula ext_modal_reserved_words)
	      		  `separatedBy` anSemi
	      c <- cBraceT
	      return (Simple_mod_decl False annoId someAxioms pos `appRange` toRange o qs c)
	   <|> return (Simple_mod_decl False annoId [] pos)
	<|>
	do tmp <- asKey timeS
	   k <- mKey 
	   (annoId, ks) <- separatedBy (annoParser simpleId) anComma
	   let pos = catRange $ k : ks
	   do o <- oBraceT
	      (someAxioms, qs) <- annoParser (formula ext_modal_reserved_words)
	      		  `separatedBy` anSemi
	      c <- cBraceT
	      return (Simple_mod_decl True annoId someAxioms pos `appRange` toRange o qs c)
	   <|> return (Simple_mod_decl True annoId [] pos)
	<|>
	do k <- nKey
	   (annoId, ks) <- separatedBy (annoParser simpleId) anComma
	   let pos = catRange $ k : ks
	   return (Nominal_decl annoId pos)

instance AParsable EM_BASIC_ITEM where 
aparser = basicItemParser 

{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Wiebke Herding and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Parser for modal logic extension of CASL
-}


module Modal.Parse_AS where
import Common.AnnoState
import Common.Id
import Common.Token
import Common.Keywords
import Common.Lexer
import Modal.AS_Modal
import Common.AS_Annotation
import Common.Lib.Parsec


boxKey, diamondKey :: AParser Token
boxKey = asKey boxS
diamondKey = asKey diamondS

modalFormula :: [String] -> AParser M_FORMULA
modalFormula k = 
	      do c <- boxKey
	         f <- primFormula k
		 return (Box None f [tokPos c])
              <|> 
	      do c <- diamondKey
		 f <- primFormula k
		 return (Diamond None f [tokPos c])

instance Parsable M_FORMULA where
  aparser = modalFormula






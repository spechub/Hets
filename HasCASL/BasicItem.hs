module BasicItem where

import Ast
import Id
import Lexer
import Maybe
import Parsec
import ParseTerm
import ParseType
import Token
import Term
import Type

sigItems = sortItems

basicItem = sigItems

basicItems = do { b <- basicItem
		; option ([b]) (do { l <- basicItems
				   ; return (b:l)
				   })
		}

basicSpec = do { ann;
		 basicItems
	       }




















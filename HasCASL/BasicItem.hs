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

sigItems ast = do {s <- sortItems
		  ; return (s:ast)
		  } 

basicItem = sigItems

-- basicItem :: Ast -> Parser Ast
basicItems ast = do { ast' <- basicItem ast;
		      option (ast') (basicItems ast')
		    }

basicSpec ast = do { ann;
		     basicItems ast
		   }




















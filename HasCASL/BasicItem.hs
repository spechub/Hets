module BasicItem where

import Id
import Lexer
import LocalEnv
import Maybe
import Parsec
import ParseTerm
import ParseType
import Token
import Term
import Type
import SortItem
-- import OpItem
import VarItem
		   
sigItems = sortItems -- <|> opItems

basicItem = sigItems

basicItem :: Ast -> Parser Ast
basicItems ast = do { ast' <- basicItem ast;
		      option (ast') (basicItems ast')
		    }

basicSpec ast = do { ann;
		     basicItems ast
		   }




















module Formula where

import Id
import Lexer
import Token
import AS_Basic_CASL
import Parsec

varStr = "var"
predStr = "pred"
opStr = "op"
exStr = "exists"
allStr = "forall"
uniqueSuffix = "!"
inStr = "in"
asStr = "as"
middleDotStr = "\183"
dotChar = '.'
exEqual = string "=e="

simpleTerm :: Parser TERM
simpleTerm = fmap Mixfix_token (makeToken(scanFloat <|> scanString 
		       <|>  scanQuotedChar <|> scanDotWords <|> scanWords 
		       <|>  scanSigns)) 


term = simpleTerm

formula = fmap Mixfix_formula term

dot = makeToken (single (keySign (oneOf (dotChar:middleDotStr))))
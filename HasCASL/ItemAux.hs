module ItemAux where

import Id(Token())
import Lexer
import Token
import Parsec
import LocalEnv

isStartKeyword s = s `elem` ([".","\183"] ++ casl_reserved_words)

pluralKeyword s = makeToken (string s <++> option "" (string "s"))

optSemi = bind (\ x y -> (x, y)) (option Nothing (fmap Just semi)) ann

dot = skip (keySign (oneOf ".\183") <?> "dot")
bar = skip (keySign (char '|'))

lookAheadItemKeyword :: Ast -> Parser Ast
lookAheadItemKeyword ast = 
    do { c <- lookAhead (many (oneOf (['0'..'9'] ++ "'" ++ caslLetters))
			 <|> many (oneOf signChars))
       ; if isStartKeyword c then return ast else unexpected c
       }

itemAux :: (Ast -> Token -> Parser Ast) -> Ast -> Token -> Parser Ast
itemAux itemParser ast key = 
    do { ast' <- itemParser ast key
       ; (m, an) <- optSemi
       ; let ast'' = if null an then ast' else addAn ast' an
	 in case m of Nothing -> return ast''
                      Just key' -> try (lookAheadItemKeyword ast'')
	                           <|> itemAux itemParser ast'' key'
       }

----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPParser where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language

import GMPAS

-----------------------------------------------------------
-- The Parser Things
-----------------------------------------------------------
par5er :: Parser String
par5er = do
    do try(string "F"); return "F"
    <|> do try(string "T"); return "T"
    <|> do try(string "~"); return "Not"
    <|> do try(string"/\\") ; return "And"
    <|> do try(string "\\/"); return "Or"
    <|> do try(string "->"); return "If"
    <|> do try(string "<-"); return "Fi"
    <|> do try(string "<->"); return "Iff"
    <?> "GMPParser.par5er"

{- the parser should actually look somewhat like the following
par5er :: Parser Formula
par5er = do Text.ParserCombinators.Parsec.try(string "F"); 
            return F
     <|> do Text.ParserCombinators.Parsec.try(string "T"); 
            return T
     <|> do Text.ParserCombinators.Parsec.try(string "~"); 
            return Neg
     <|> do Text.ParserCombinators.Parsec.try(string "/\\"); 
            return And
     <|> do Text.ParserCombinators.Parsec.try(string "\\/"); 
            return Or
     <|> do Text.ParserCombinators.Parsec.try(string "->"); 
            return If
     <|> do try(string "<-"); 
            return Fi

-}

runLex :: Show a => Parser a -> String -> IO ()
runLex p input = run (do {
    whiteSpace
    ; x <- p
    ; eof
    ; return x
    }) input

run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
                Left err -> do{ putStr "parse error at "
                                ; print err
                              }
                Right x -> print x

----------------------------------------------------------------
-- Formulae
----------------------------------------------------------------
{-
form :: Parser Formula
form = choice
	[ not
	, and
	, or
	, ifimpl
	, fiimpl
	, iffimpl
	, mop
	]
	<?> "formulae"

not = do
	try (symbol "~") ;
	f <- form ;
	return Not(f)

and = do 
	try (symbol "/"; symbol "\\") ;
	f <- form ;

-- not complete
-}
----------------------------------------------------------------
-- The lexer
----------------------------------------------------------------
lexer            = P.makeTokenParser gmpDef

lexeme          = P.lexeme lexer
parens          = P.parens lexer
braces          = P.braces lexer
semiSep         = P.semiSep lexer
semiSep1        = P.semiSep1 lexer
commaSep        = P.commaSep lexer
commaSep1       = P.commaSep1 lexer
whiteSpace      = P.whiteSpace lexer
symbol          = P.symbol lexer
identifier      = P.identifier lexer
reserved        = P.reserved lexer
natural         = P.natural lexer


gmpDef
    = haskellStyle
    { identStart        = letter
    , identLetter       = alphaNum <|> oneOf "_'" -- ???
    , opStart           = opLetter gmpDef
    , opLetter          = oneOf "\\->/~[]"
    , reservedOpNames   = ["~","->","<-","<->","/\\","\\/","[]"]
    }
----------------------------------------------------------------
-- ???
----------------------------------------------------------------

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
-- A program is simply a formulae
-----------------------------------------------------------
program
    = do{ whiteSpace
        ; f <- form
        ; return f
        }
{-
----------------------------------------------------------------
-- Formulae
----------------------------------------------------------------
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
    , reservedOpNames   = ["~","\\","->","<-","<->","/\\","\\/","[]"]
    }
----------------------------------------------------------------
-- ???
----------------------------------------------------------------

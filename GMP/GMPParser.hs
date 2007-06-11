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
par5er :: Parser Formula -- main parser to parse the infix/primitive formulae
par5er =
    do f <- prim; option (f) (inf f)
    <?> "GMPParser.par5er"

inf :: Formula -> Parser Formula -- infix parser
inf f1 =
        do try(string "/\\"); f2 <- par5er; return $ And f1 f2
    <|> do try(string "\\/"); f2 <- par5er; return $ Or f1 f2
    <|> do try(string "->");  f2 <- par5er; return $ If f1 f2
    <|> do try(string "<-");  f2 <- par5er; return $ Fi f1 f2
    <|> do try(string "<->"); f2 <- par5er; return $ Iff f1 f2
    <?> "GMPParser.inf"

prim :: Parser Formula -- primitive parser
prim = 
        do try(string "F"); return F
    <|> do try(string "T"); return T
    <|> do try(string "~"); f <- par5er; return $ Neg f
    <?> "GMPParser.prim"

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

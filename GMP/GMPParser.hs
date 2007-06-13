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
-- The Different Parsers
-----------------------------------------------------------
par5er :: Parser Formula -- main parser to parse the infix/primitive formulae
par5er =
    do f <- prim; option (f) (inf f)
    <?> "GMPParser.par5er"

junc :: Parser Junctor -- junctor parser
junc =
        do try(string "/\\"); return And
    <|> do try(string "\\/"); return Or
    <|> do try(string "->");  return If
    <|> do try(string "<->");  return Iff
    <|> do try(string "<-"); return Fi
    <?> "GMPParser.junc"

inf :: Formula -> Parser Formula -- infix parser
inf f1 =
        do iot <- junc; f2 <- par5er; return $ Junctor f1 iot f2
    <?> "GMPParser.inf"

prim :: Parser Formula -- primitive parser
prim = 
        do try(string "F"); return F
    <|> do try(string "T"); return T
    <|> do try(string "~"); f <- par5er; return $ Neg f
    <|> do char '('; f <- par5er; char ')'; return f
    <|> do char '['; i <- ind; char ']'; f <-par5er; return $ Mapp (Mop i Square) f
    <|> do char '<'; i <- ind; char '>'; f <-par5er; return $ Mapp (Mop i Angle) f
    <?> "GMPParser.prim"

ind :: Parser Mindex  -- modal index parser (as string for now)
ind = many1 (letter <?> "GMPParser.ind")

runLex :: Show a => Parser a -> String -> IO ()
runLex p input = run (do 
    whiteSpace
    ; x <- p
    ; n <- newline -- the input is taken from a line of a file and the \n character is still present after parsing the formula
    ; eof
    ; return x
    ) input

run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
                Left err -> do{ putStr "parse error at "
                                ; print err
                              }
                Right x -> print x

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
whiteSpace      = P.whiteSpace lexer -- used
symbol          = P.symbol lexer
identifier      = P.identifier lexer
reserved        = P.reserved lexer
natural         = P.natural lexer


gmpDef
    = haskellStyle
    { identStart        = letter
    , identLetter       = alphaNum <|> oneOf "_'" -- ???
    , opStart           = opLetter gmpDef
    , opLetter          = oneOf "\\-</~[]"
    , reservedOpNames   = ["~","->","<-","<->","/\\","\\/","[]"]
    }
----------------------------------------------------------------
-- 
----------------------------------------------------------------

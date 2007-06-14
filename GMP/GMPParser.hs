----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPParser where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language

import qualified Data.Set as Set

import GMPAS
----------------------------------------------------------------
-- Modal Logic Class
----------------------------------------------------------------
class ModalLogic a where
    parseIndex :: Parser a

instance ModalLogic () where        -- unit parsed Mindex
    parseIndex = return ()
instance ModalLogic Integer where   -- integer parsed Mindex
    parseIndex = natural
instance ModalLogic Kars where
    parseIndex =  do l <- letter; Kars i <- parseIndex; return (Kars (l:i))
              <|> do return (Kars [])

-- to be changed so that it works on BitString ... :

{-parse i = do
    char '0'; BitString n <- parse(i+1); return(BitString(setBit n i)) ... or so-}
instance ModalLogic [Integer] where -- bit-string parsed Mindex
    parseIndex =  do try(char '0'); i <- parseIndex; return (0:i)
              <|> do try(char '1'); i <- parseIndex; return (1:i)
              <|> return []

-----------------------------------------------------------
-- The Different Parsers for general Formula Type
-----------------------------------------------------------
par5er :: ModalLogic a => Parser (Formula a) -- main parser to parse the infix/primitive formulae
par5er = do f <- prim; option (f) (inf f)
      <?> "GMPParser.par5er"

junc :: Parser Junctor -- junctor parser
junc =  do try(string "/\\"); whiteSpace; return And
    <|> do try(string "\\/"); whiteSpace; return Or
    <|> do try(string "->");  whiteSpace; return If
    <|> do try(string "<->"); whiteSpace; return Iff
    <|> do try(string "<-");  whiteSpace; return Fi
    <?> "GMPParser.junc"

inf :: ModalLogic a => (Formula a)-> Parser (Formula a)-- infix parser
inf f1 =
    do iot <- junc; f2 <-par5er; return $ Junctor f1 iot f2
    <?> "GMPParser.inf"

prim :: ModalLogic a => Parser (Formula a)  -- primitive parser
prim = 
        do try(string "F"); whiteSpace; return F;
    <|> do try(string "T"); whiteSpace; return T;
    <|> do try(string "~"); whiteSpace; f <- par5er; return $ Neg f
    <|> do try(char '('); whiteSpace; f <- par5er; whiteSpace; char ')'; whiteSpace; return f
    <|> do try(char '['); whiteSpace; i <- parseIndex; whiteSpace; char ']'; whiteSpace; f <-par5er; return $ Mapp (Mop i Square) f
    <|> do try(char '<'); whiteSpace; i <- parseIndex; whiteSpace; char '>'; whiteSpace; f <-par5er; return $ Mapp (Mop i Angle) f
    <?> "GMPParser.prim"
----------------------------------------------------------------
-- Run GMP parser & print
----------------------------------------------------------------
runLex :: Show b => Parser b -> String -> IO ()
runLex p input = run (do 
    whiteSpace
    ; x <- p
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
    , opLetter          = oneOf "\\-</~[]"
    , reservedOpNames   = ["~","->","<-","<->","/\\","\\/","[]"]
    }
----------------------------------------------------------------
----------------------------------------------------------------

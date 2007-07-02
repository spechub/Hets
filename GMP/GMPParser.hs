-------------------------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------

module GMPParser where

import Text.ParserCombinators.Parsec
import Lexer
import GMPAS
-------------------------------------------------------------------------------
-- Parser for polymorphic (Formula a) Type
-------------------------------------------------------------------------------
par5er :: Parser a -> Parser (Formula a)                         -- main parser
par5er pa = do f <- prim pa; option (f) (inf pa f)
         <?> "GMPParser.par5er"

junc :: Parser Junctor                                        -- junctor parser
junc =  do try(string "/\\"); whiteSpace; return And
    <|> do try(string "\\/"); whiteSpace; return Or
    <|> do try(string "->");  whiteSpace; return If
    <|> do try(string "<->"); whiteSpace; return Iff
    <|> do try(string "<-");  whiteSpace; return Fi
    <?> "GMPParser.junc"

inf :: Parser a -> (Formula a)-> Parser (Formula a)             -- infix parser
inf pa f1 =
    do iot <- junc; f2 <-par5er pa; return $ Junctor f1 iot f2
    <?> "GMPParser.inf"

varp :: CharParser st Char                               -- lower letter parser
varp = let isAsciiLower c = c >= 'a' && c <= 'z'
       in satisfy isAsciiLower
    
prim :: Parser a -> Parser (Formula a)                      -- primitive parser
prim pa = 
        do try(string "F")
           whiteSpace
           return F
    <|> do try(string "T")
           whiteSpace
           return T
    <|> do try(string "~")
           whiteSpace
           f <- par5er pa
           return $ Neg f
    <|> do try(char '(')
           whiteSpace
           f <- par5er pa
           whiteSpace
           char ')'
           whiteSpace
           return f
    <|> do try(char '[')
           whiteSpace
           i <- pa
           whiteSpace
           char ']'
           whiteSpace
           f <-par5er pa
           return $ Mapp (Mop i Square) f
    <|> do try(char '<')
           whiteSpace
           i <- pa
           whiteSpace
           char '>'
           whiteSpace
           f <- par5er pa
           return $ Neg (Mapp (Mop i Square) (Neg f))  -- Mapp (Mop i Angle) f
    <|> do v <- varp
           i <- natural
           whiteSpace
           return $ Var v i
    <?> "GMPParser.prim"
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

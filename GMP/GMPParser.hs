-------------------------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------

module GMPParser where

import Text.ParserCombinators.Parsec
import Lexer
import ModalLogic
import GMPAS

import GMPSAT()
-------------------------------------------------------------------------------
-- Parser for polymorphic (Formula a) Type
-------------------------------------------------------------------------------
par5er :: ModalLogic a b => Parser (Formula a)                   -- main parser
par5er = do f <- prim; option (f) (inf f)
      <?> "GMPParser.par5er"

junc :: Parser Junctor                                        -- junctor parser
junc =  do try(string "/\\"); whiteSpace; return And
    <|> do try(string "\\/"); whiteSpace; return Or
    <|> do try(string "->");  whiteSpace; return If
    <|> do try(string "<->"); whiteSpace; return Iff
    <|> do try(string "<-");  whiteSpace; return Fi
    <?> "GMPParser.junc"

inf :: ModalLogic a b => (Formula a)-> Parser (Formula a)       -- infix parser
inf f1 =
    do iot <- junc; f2 <-par5er; return $ Junctor f1 iot f2
    <?> "GMPParser.inf"

prim :: ModalLogic a b => Parser (Formula a)                -- primitive parser
prim =  do try(string "F")
           ;whiteSpace
           ;return F
    <|> do try(string "T")
           ;whiteSpace
           ;return T
    <|> do try(string "~")
           ;whiteSpace
           ;f <- par5er
           ;return $ Neg f
    <|> do try(char '(')
           ;whiteSpace
           ;f <- par5er
           ;whiteSpace
           ;char ')'
           ;whiteSpace
           ;return f
    <|> do try(char '[')
           ;whiteSpace
           ;i <- parseIndex
           ;whiteSpace
           ;char ']'
           ;whiteSpace
           ;f <-par5er
           ;return $ Mapp (Mop i Square) f
    <|> do try(char '<')
           ;whiteSpace
           ;i <- parseIndex
           ;whiteSpace
           ;char '>'
           ;whiteSpace
           ;f <- par5er
           ;return $ Neg (Mapp (Mop i Square) (Neg f))  -- Mapp (Mop i Angle) f
    <?> "GMPParser.prim"
-------------------------------------------------------------------------------
-- Funtion to run parser & print
-------------------------------------------------------------------------------
runLex :: (Ord a, Show a) => Parser (Formula a) -> String -> IO ()
runLex p input = run (do 
    whiteSpace
    ; x <- p
    ; eof
    ; return x
    ) input

run :: (Ord a, Show a) => Parser (Formula a) -> String -> IO ()
run p input
        = case (parse p "" input) of
                Left err -> do putStr "parse error at "
                               ;print err
                Right x ->  do --let ls = guessPV x -----------------------------
                               --;let h = head(ls) ------------------------------
                               --;print h ------------ FOR TESTING --------------
                               --;let lro = ROfromPV (h) ----------------------------
                               --; print lro ------------------------------------
                               ;print x
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------
module GMP.GMPParser where

import GMP.GMPAS
import GMP.Lexer
import Text.ParserCombinators.Parsec

par5er :: GenParser Char st a -> GenParser Char st (Formula a)
par5er pa = implFormula pa

parenFormula :: GenParser Char st a -> GenParser Char st (Formula a)
parenFormula pa =  do try (char '(')
                      whiteSpace
                      f <- par5er pa
                      whiteSpace
                      char ')'
                      whiteSpace
                      return f
               <?> "GMPParser.parenFormula"

varp :: CharParser st Char                               -- lower letter parser
varp = let isAsciiLower c = c >= 'a' && c <= 'z'
       in satisfy isAsciiLower

primFormula :: GenParser Char st a -> GenParser Char st (Formula a)
primFormula pa =  do try (string "T")
                     whiteSpace
                     return T
              <|> do try (string "F")
                     whiteSpace
                     return F
              <|> do f <- parenFormula pa
                     return f
              <|> do try (string "~")
                     whiteSpace
                     f <- primFormula pa
                     return $ Neg f
              <|> do try (char '<')
                     whiteSpace
                     i <- pa
                     whiteSpace
                     char '>'
                     whiteSpace
                     f <- primFormula pa
                     return $ Mapp (Mop i Angle) f
              <|> do try (char '[')
                     whiteSpace
                     i <- pa
                     whiteSpace
                     char ']'
                     whiteSpace
                     f <- primFormula pa
                     return $ Mapp (Mop i Square) f
              <|> do v <- varp
                     i <- natural
                     whiteSpace
                     return $ Var v i
              <?> "GMPParser.primFormula"

andFormula :: GenParser Char st a -> GenParser Char st (Formula a)
andFormula pa = do 
    f <- primFormula pa
    option f $ do 
      try (string "/\\")
      whiteSpace
      g <- andFormula pa
      return $ Junctor f And g
  <?> "GMPParser.andFormula"

orFormula :: GenParser Char st a -> GenParser Char st (Formula a)
orFormula pa = do
    f <- andFormula pa
    option f $ do 
      try (string "\\/")
      whiteSpace
      g <- orFormula pa
      return $ Junctor f Or g
  <?> "GMPParser.orFormula"

implFormula :: GenParser Char st a -> GenParser Char st (Formula a)
implFormula pa = do
    f <- orFormula pa
    option f ((do 
      try (string "->")
      whiteSpace
      i <- implFormula pa
      return $ Junctor f If i)
                <|> do try (string "<->")
                       whiteSpace
                       i <- orFormula pa
                       return $ Junctor f Iff i
                <|> do try (string "<-")
                       whiteSpace
                       i <- orFormula pa
                       return $ Junctor f Fi i
                <|> do return f
                <?> "GMPParser.implFormula")
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

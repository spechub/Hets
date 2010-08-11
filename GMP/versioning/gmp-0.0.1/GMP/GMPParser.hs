{- | Module     : $Header$
 -  Description : Parser implementation for parsing formulas
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : GPLv2 or higher
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Provides the implementation of the generic parser for the formula datatype
 -  with binding order on the junctors -}
module GMP.GMPParser where

import GMP.GMPAS
import GMP.Lexer
import Text.ParserCombinators.Parsec

-- | Main parser
par5er :: GenParser Char st a -> GenParser Char st (Formula a)
par5er pa = implFormula pa

-- | Parser for un-parenthesizing a formula
parenFormula :: GenParser Char st a -> GenParser Char st (Formula a)
parenFormula pa =  do try (char '(')
                      whiteSpace
                      f <- par5er pa
                      whiteSpace
                      char ')'
                      whiteSpace
                      return f
               <?> "GMPParser.parenFormula"

-- | Parse the leading character in a variable
varp :: CharParser st Char
varp = let isAsciiLower c = c >= 'a' && c <= 'z'
       in satisfy isAsciiLower

-- | Parse the possible integer index of a variable
varIndex :: GenParser Char st (Maybe Integer)
varIndex =  do i <- try natural
               whiteSpace
               return $ Just i
        <|> do whiteSpace
               return $ Nothing
        <?> "GMPParser.varIndex"

{- | Parse a primitive formula i.e. a formula that may be :
 -     T, F, ~f, <i>f, [i]f, #* , where i stands for an index, f for a
 - formula, # for a lowercase letter between 'a' and 'z' and * for a
 - (possibly empty) series of digits i.e. and integer -}
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
                     i <- varIndex
                     return $ Var v i
              <?> "GMPParser.primFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: GenParser Char st a -> GenParser Char st (Formula a)
andFormula pa = do
    f <- primFormula pa
    option f $ do
      try (string "/\\")
      whiteSpace
      g <- andFormula pa
      return $ Junctor f And g
  <?> "GMPParser.andFormula"

-- | Parser for disjunction - used for handling binding order
orFormula :: GenParser Char st a -> GenParser Char st (Formula a)
orFormula pa = do
    f <- andFormula pa
    option f $ do
      try (string "\\/")
      whiteSpace
      g <- orFormula pa
      return $ Junctor f Or g
  <?> "GMPParser.orFormula"

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: GenParser Char st a -> GenParser Char st (Formula a)
implFormula pa = do
    f <- orFormula pa
    option f ((do try (string "->")
                  whiteSpace
                  i <- implFormula pa
                  return $ Junctor f If i)
          <|> do try (string "<->")
                 whiteSpace
                 i <- implFormula pa
                 return $ Junctor f Iff i
          <|> do try (string "<-")
                 whiteSpace
                 i <- implFormula pa
                 return $ Junctor f Fi i
          <|> do return f
          <?> "GMPParser.implFormula")

{- | Module     : $Header$
 -  Description : Implementation of logic formula parser
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the generic parser for the L formula datatype
 -}
module GMP.GMPParser where

import GMP.Generic
import Text.ParserCombinators.Parsec

-- | Main parser
par5er :: GenParser Char st a -> GenParser Char st (L a)
par5er pa = implFormula pa

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: GenParser Char st a -> GenParser Char st (L a)
implFormula pa = do
    f <- orFormula pa
    option f (do try (string "->")
                 spaces
                 i <- implFormula pa
                 return $ Or (Neg f) i
          <|> do try (string "<->")
                 spaces
                 i <- implFormula pa
                 return $ And (Or (Neg f) i) (Or f (Neg i))
          <|> do try (string "<-")
                 spaces
                 i <- implFormula pa
                 return $ Or f (Neg i)
          <|> do return f
          <?> "GMPParser.implFormula")

-- | Parser for disjunction - used for handling binding order
orFormula :: GenParser Char st a -> GenParser Char st (L a)
orFormula pa = do
    f <- andFormula pa
    option f $ do
      try (string "\\/")
      spaces
      g <- orFormula pa
      return $ Or f g
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: GenParser Char st a -> GenParser Char st (L a)
andFormula pa = do
    f <- primFormula pa
    option f $ do
      try (string "/\\")
      spaces
      g <- andFormula pa
      return $ And f g
  <?> "GMPParser.andFormula"

          
{- | Parse a primitive formula i.e. a formula that may be :
 -     T, F, ~f, <i>f, [i]f, #* , where i stands for an index, f for a
 - formula, # for a lowercase letter between 'a' and 'z' and * for a
 - (possibly empty) series of digits i.e. and integer -}
primFormula :: GenParser Char st a -> GenParser Char st (L a)
primFormula pa =  do try (string "T")
                     spaces
                     return T
              <|> do try (string "F")
                     spaces
                     return F
              <|> do f <- parenFormula pa
                     return f
              <|> do try (string "~")
                     spaces
                     f <- primFormula pa
                     return $ Neg f
              <|> do try (char '<')
                     spaces
                     i <- pa
                     spaces
                     char '>'
                     spaces
                     f <- primFormula pa
                     return $ M i f
{- we could use smt like
                     let flag = defaultMop pa
                     let res = if flag
                               then return $ Neg M i Neg f
                               else return $ M i f
                     return res
-}
              <|> do try (char '[')
                     spaces
                     i <- pa
                     spaces
                     char ']'
                     spaces
                     f <- primFormula pa
                     return $ M i f
{- we could use something similar to
                     let flag = defaultMop pa
                     let res = if flag
                               then M i f
                               else Neg M i Neg f
                     return res
-}
              <|> do try (char 'p')
                     i <- atomIndex
                     return $ Atom (fromInteger i)
              <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
parenFormula :: GenParser Char st a -> GenParser Char st (L a)
parenFormula pa =  do try (char '(')
                      spaces
                      f <- par5er pa
                      spaces
                      char ')'
                      spaces
                      return f
               <?> "GMPParser.parenFormula"

-- | Parse integer number
natural :: GenParser Char st Integer
natural = do t1 <- digit
             tr <- try (many digit)
             return $ read (t1:tr)

-- | Parse the possible integer index of a variable
atomIndex :: GenParser Char st Integer
atomIndex =  do i <- try natural
                spaces
                return $ i
         <?> "GMPParser.atomIndex"

-- | Parser for the different modal logic indexes

-- parseCindex :: Parser C

-- parseGindex :: Parser GML

-- parseHMindex :: Parser HM

-- parseKKDindex :: Parser a

-- parsePindex :: Parser P

-- | Function to set the default modal operator
defaultMop :: GenParser Char st a -> Bool 
defaultMop _ = True
{-
defaultMOP (x::Parser K) = 1
defaultMOP (x::Parser KD) = 1
defaultMOP (x::Parser HM) = 0
defaultMOP (x::Parser Mon) = 1
defaultMOP (x::Parser C) =
defaultMOP (x::Parser G) =
defaultMOP (x::Parser P) =
-}

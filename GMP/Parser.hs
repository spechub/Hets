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
module GMP.Parser where

import GMP.Generic
import Text.ParserCombinators.Parsec

-- | Main parser
par5er :: GenParser Char st a -> GenParser Char st (L a)
par5er pa = implFormula pa

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: GenParser Char st a -> GenParser Char st (L a)
implFormula pa = do
    f <- orFormula pa
    option f (do string "->"
                 spaces
                 i <- implFormula pa
                 return $ Or (Neg f) i
          <|> do string "<->"
                 spaces
                 i <- implFormula pa
                 return $ And (Or (Neg f) i) (Or f (Neg i))
          <|> do string "<-"
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
      string "\\/"
      spaces
      g <- orFormula pa
      return $ Or f g
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: GenParser Char st a -> GenParser Char st (L a)
andFormula pa = do
    f <- primFormula pa
    option f $ do
      string "/\\"
      spaces
      g <- andFormula pa
      return $ And f g
  <?> "GMPParser.andFormula"

          
{- | Parse a primitive formula i.e. a formula that may be :
 -     T, F, ~f, <i>f, [i]f, #* , where i stands for an index, f for a
 - formula, # for a lowercase letter between 'a' and 'z' and * for a
 - (possibly empty) series of digits i.e. and integer -}
primFormula :: GenParser Char st a -> GenParser Char st (L a)
primFormula pa =  do string "T"
                     spaces
                     return T
              <|> do string "F"
                     spaces
                     return F
              <|> do f <- parenFormula pa
                     return f
              <|> do string "~"
                     spaces
                     f <- primFormula pa
                     return $ Neg f
              <|> do char '<'
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
              <|> do char '['
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
              <|> do char 'p'
                     i <- atomIndex
                     return $ Atom (fromInteger i)
              <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
parenFormula :: GenParser Char st a -> GenParser Char st (L a)
parenFormula pa =  do char '('
                      spaces
                      f <- par5er pa
                      spaces
                      char ')'
                      spaces
                      return f
               <?> "GMPParser.parenFormula"

-- | Parse integer number
natural :: GenParser Char st Integer
natural = fmap read $ many1 digit 

-- | Parse the possible integer index of a variable
atomIndex :: GenParser Char st Integer
atomIndex =  do i <- try natural
                spaces
                return $ i
         <?> "GMPParser.atomIndex"

-- | Parsers for the different modal logic indexes

parseCindex :: Parser C
parseCindex =  do -- checks whether there are more numbers to be parsed
                  let stopParser =  do char ','
                                       return False
                                <|> do char ']'
                                       return True
                                <|> do char '>'
                                       return True
                                <?> "Parser.parseCindex.stop"                  
                  -- checks whether the index is of the for x1,..,x&
                  let normalParser l =  do x <- natural
                                           let n = fromInteger x
                                           q <- stopParser
                                           spaces
                                           case q of
                                             False -> normalParser (n:l)
                                             _     -> return (n:l)
                                    <?> "Parser.parseCindex.normal"
                  res <- normalParser []
                  return $ C res
           <|> do -- checks whether the index is of the form "n..m"
                  let shortParser =  do x <- natural
                                        let n = fromInteger x
                                        spaces
                                        string ".."
                                        spaces
                                        y <- natural
                                        let m = fromInteger y
                                        return $ [n..m]
                                 <?> "Parser.parseCindex.short"
                  res <- shortParser
                  return $ C res
           <?> "Parser.parseCindex"

parseGindex :: Parser G
parseGindex = do n <- natural
                 return $ G (fromInteger n)

parseHMindex :: Parser HM
parseHMindex = do c <- anyChar
                  return $ HM c

parseKindex :: Parser K
parseKindex = return K

parseKDindex ::Parser KD
parseKDindex = return KD

parsePindex :: Parser P
parsePindex = 
    do x <- natural
       let auxP n =  do char '/'
                        m<-natural
                        return $ toRational (fromInteger n/fromInteger m)
                 <|> do char '.'
                        m<-natural
                        let noDig n
                              | n<10 = 1
                              | n>=10 = 1 + noDig (div n 10)
                        let rat n = toRational(fromInteger n / 
                                               fromInteger (10^(noDig n)))
                        let res = toRational n + rat m
                        return res
                 <|> do return $ toRational n
                 <?> "Parser.parsePindex.auxP"
       aux <- auxP x
       return $ P aux

parseMindex :: Parser Mon
parseMindex = return Mon


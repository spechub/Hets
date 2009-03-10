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
import Text.ParserCombinators.Parsec

import GMP.Generic
import GMP.Logics

data ModalOperator = Sqr | Ang | None
    deriving Eq

-- | Main parser
parser :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
parser flag pa = implFormula flag pa

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
implFormula flag pa = do
    f <- orFormula flag pa
    option f (do string "->"
                 spaces
                 i <- implFormula flag pa
                 return $ Or (Neg f) i
          <|> do try(string "<->")
                 spaces
                 i <- implFormula flag pa
                 return $ And (Or (Neg f) i) (Or f (Neg i))
          <|> do string "<-"
                 spaces
                 i <- implFormula flag pa
                 return $ Or f (Neg i)
          <|> do return f
          <?> "GMPParser.implFormula")

-- | Parser for disjunction - used for handling binding order
orFormula :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
orFormula flag pa = do
    f <- andFormula flag pa
    option f $ do
      string "\\/"
      spaces
      g <- orFormula flag pa
      return $ Or f g
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
andFormula flag pa = do
    f <- primFormula flag pa
    option f $ do
      string "/\\"
      spaces
      g <- andFormula flag pa
      return $ And f g
  <?> "GMPParser.andFormula"

          
{- | Parse a primitive formula: T, F, ~f, <i>f, [i]f, p*, 
 -   where i stands for an index, f for a formula and 
 -   * for a series of digits i.e. and integer -}
primFormula :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
primFormula flag pa =  
                  do string "T"
                     spaces
                     return T
              <|> do string "F"
                     spaces
                     return F
              <|> do f <- parenFormula flag pa
                     return f
              <|> do string "~"
                     spaces
                     f <- primFormula flag pa
                     return $ nneg f
              <|> do char '<'
                     spaces
                     i <- pa
                     spaces
                     char '>'
                     spaces
		     f <- sepBy1 (primFormula flag pa) (char ',')
                     -- restrict to the default modal operator
                     case flag of
                       Ang -> return $ M i f
                       Sqr -> return $ Neg (M i (map nneg f))
                       _   -> return $ M i f
              <|> do char '['
                     spaces
                     i <- pa
                     spaces
                     char ']'
                     spaces
		     f <- sepBy1 (primFormula flag pa) (char ',')
                     -- restrict to the default modal operator
                     case flag of
                       Sqr -> return $ M i f
                       Ang -> return $ Neg (M i (map nneg f))
                       _   -> return $ M i f
              <|> do char 'p'
                     i <- atomIndex
                     return $ Atom (fromInteger i)
              <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
parenFormula :: ModalOperator -> GenParser Char st a -> GenParser Char st (L a)
parenFormula flag pa =  
                   do char '('
                      spaces
                      f <- parser flag pa
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
                                <|> do char '}'
                                       return True
                                <?> "Parser.parseCindex.stop"                  
                  -- checks whether the index is of the form x1,..,x&
                  let normalParser l =  do x <- natural
                                           let n = fromInteger x
                                           spaces
                                           q <- stopParser
                                           spaces
                                           case q of
                                             False -> normalParser (n:l)
                                             _     -> return (n:l)
                                    <?> "Parser.parseCindex.normal"
                  char '{'
                  res <- try(normalParser [])
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
                  res <- try(shortParser)
                  return $ C res
           <?> "Parser.parseCindex"

parseGindex :: Parser G
parseGindex = do n <- natural
                 return $ G (fromInteger n)

parseHMindex :: Parser HM
parseHMindex =  do c <- letter
                   return $ HM c
            <?> "Parser.parseHMindex"

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

parseConindex :: Parser Con
parseConindex = return Con


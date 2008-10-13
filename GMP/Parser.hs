{- | Module     : $Header$
 -  Description : Implementation of logic formula parser
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the generic parser for the Boole datatype
 -}
{-# OPTIONS -fglasgow-exts #-}
module Parser where

import Text.ParserCombinators.Parsec

-- import GenericSequent
import ModalLogic
import CombLogic

data ModalOperator = Sqr | Ang | None deriving Eq

-- | Main parser
-- par5er :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
par5er flag logics = implFormula flag logics

-- | Parser which translates all implications in disjunctions & conjunctions
-- implFormula :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
implFormula flag logics = do
    f <- orFormula flag logics
    option f (do string "->"
                 spaces
                 i <- implFormula flag logics
                 return $ Not (And f (Not i))
          <|> do try(string "<->")
                 spaces
                 i <- implFormula flag logics
                 return $ And (Not (And f (Not i))) (Not (And (Not f) i))
          <|> do string "<-"
                 spaces
                 i <- implFormula flag logics
                 return $ And (Not f) i
          <|> do return f
          <?> "GMPParser.implFormula")

-- | Parser for disjunction - used for handling binding order
-- orFormula :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
orFormula flag logics = do
    f <- andFormula flag logics
    option f $ do
      string "\\/"
      spaces
      g <- orFormula flag logics
      return $ Not (And (Not f) (Not g))
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
-- andFormula :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
andFormula flag logics = do
    f <- primFormula flag logics
    option f $ do
      string "/\\"
      spaces
      g <- andFormula flag logics
      return $ And f g
  <?> "GMPParser.andFormula"

          
{- | Parse a primitive formula: T, F, ~f, <i>f, [i]f, 
 -   where i stands for an index, f for a formula/boolean expression -}
-- primFormula :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
primFormula flag logics =  do string "T"
                              spaces
                              return T
                       <|> do string "F"
                              spaces
                              return F
                       <|> do f <- parenFormula flag logics
                              return f
                       <|> do string "~"
                              spaces
                              f <- primFormula flag logics
                              return $ Not f
                       <|> do f <- modalAtom flag logics
                              return f
                       

--modalAtom :: ModalOperator -> [Int] -> GenParser Char st (Boole a)
modalAtom flag logics = do char '<'
                           spaces
                           let h = head logics
                           let t = tail logics
                           case h of
                                1 -> do parseKindex
                                        spaces
                                        char '>'
                                        spaces
                                        f <- primFormula flag $ t ++ [h]
                                        case flag of
                                          Ang -> return $ At (K f)--M i f
                                          Sqr -> return $ Not (At (K (Not f)))
                                          _   -> return $ At (K f)
{-
                                2 -> do parseKDindex
                                        spaces
                                        char '>'
                                        spaces
                                        f <- primFormula flag $ t ++ [h]
                                        case flag of
                                          Ang -> return $ At (KD f)--M i f
                                          Sqr -> return $ Not (At (KD (Not f)))
                                          _   -> return $ At (KD f)

-}
{-
                                _ -> do aux <- parseGindex
                                        return aux
-}
{-
                   <|> do char '['
                          spaces
                          i <- head pa
                          spaces
                          char ']'
                          spaces
                          f <- primFormula flag $ tail pa ++ [head pa]
                          case flag of
                            Ang -> return $ Not (At (Not (Box i f)))
                            Sqr -> return $ At (Box i f)
                            _   -> return $ At (Box i f)
-}
                       <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
-- parenFormula :: ModalOperator -> [GenParser Char st a] -> GenParser Char st (Boole a)
parenFormula flag logics = do char '('
                              spaces
                              f <- par5er flag logics
                              spaces
                              char ')'
                              spaces
                              return f
                        <?> "GMPParser.parenFormula"


-- | Parse integer number
natural :: GenParser Char st Integer
natural = fmap read $ many1 digit 

-- | Parser for Coalition Logic index
parseCindex :: Parser [Int]
parseCindex =  do -- checks whether there are more numbers to be parsed
                  let stopParser =  do char ','
                                       return False
                                <|> do char '}'
                                       return True
                                <?> "Parser.parseCindex.stop"                  
                  -- checks whether the index is of the for x1,..,x&
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
                  return $ res
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
                  return $ res
           <?> "Parser.parseCindex"

-- | Parser for Graded Modal Logic index
parseGindex :: Parser Int
parseGindex =  do n <- natural
                  return $ fromInteger n
           <?> "Parser.parseGindex"

-- | Parser for Hennesy-Milner Modal Logic index
parseHMindex :: Parser Char
parseHMindex =  do c <- letter
                   return $ c
            <?> "Parser.parseHMindex"

-- | Parser for K Modal Logic index
parseKindex :: Parser ()
parseKindex = return ()

-- | Parser for KD Modal Logic index
parseKDindex ::Parser ()
parseKDindex = return ()

-- | Parser for Probability Logic index
parsePindex :: Parser Rational
parsePindex = 
    do x <- natural
       let auxP n =  do char '/'
                        m<-natural
                        return $ toRational (fromInteger n/fromInteger m)
                 <|> do char '.'
                        m<-natural
                        let noDig n = let tmp = n<10
                                      in case tmp of
                                           True -> 1
                                           _    -> 1 + noDig (div n 10)
                        let rat n = toRational(fromInteger n / 
                                               fromInteger (10^(noDig n)))
                        let res = toRational n + rat m
                        return res
                 <|> do return $ toRational n
                 <?> "Parser.parsePindex.auxP"
       aux <- auxP x
       return $ aux

-- | Parser for Monotonic Modal Logic index
parseMindex :: Parser ()
parseMindex = return ()

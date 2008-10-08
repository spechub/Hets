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
module Parser where

import Text.ParserCombinators.Parsec

import ModalLogic
import GenericSequent
import CombLogic

{-
-- | Main parser
par5er :: [GenParser Char st a] -> GenParser Char st (Boole a)
par5er pa = implFormula pa

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: [GenParser Char st a] -> GenParser Char st (Boole a)
implFormula pa = do
    f <- orFormula pa
    option f (do string "->"
                 spaces
                 i <- implFormula pa
                 return $ Or (Neg f) i
          <|> do try(string "<->")
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
orFormula :: [GenParser Char st a] -> GenParser Char st (Boole a)
orFormula pa = do
    f <- andFormula pa
    option f $ do
      string "\\/"
      spaces
      g <- orFormula pa
      return $ Or f g
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: [GenParser Char st a] -> GenParser Char st (Boole a)
andFormula pa = do
    f <- primFormula pa
    option f $ do
      string "/\\"
      spaces
      g <- andFormula pa
      return $ And f g
  <?> "GMPParser.andFormula"

          
{- | Parse a primitive formula: T, F, ~f, <i>f, [i]f, p*, 
 -   where i stands for an index, f for a formula and 
 -   * for a series of digits i.e. and integer -}
primFormula :: GenParser Char st a -> GenParser Char st (Boole a)
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
                     return $ nneg f
              <|> do char '<'
                     spaces
                     i <- pa
                     spaces
                     char '>'
                     spaces
                     f <- primFormula pa
                     return $ M i f
              <|> do char '['
                     spaces
                     i <- pa
                     spaces
                     char ']'
                     spaces
                     f <- primFormula flag pa
                     return $ M i f
              <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
parenFormula :: GenParser Char st a -> GenParser Char st (Boole a)
parenFormula pa =  do char '('
                      spaces
                      f <- par5er flag pa
                      spaces
                      char ')'
                      spaces
                      return f
               <?> "GMPParser.parenFormula"
-}
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

-- | Main parsing unit for checking provability/satisfiability
run :: (Eq a, Form a b c) => Parser (Boole a) -> String -> IO ()
run parser input = case (parse parser "" input) of
                     Left err -> do putStr "parse error at "
                                    print err
                     Right x ->  do --putStrLn (show x{-++" <=> "++input-})
                                    let isP = provable x
                                    case isP of
                                       True -> putStrLn "... is Provable"
                                       _    -> let isS = sat x
                                               in case isS of
                                                    True -> putStrLn "... is not Provable but Satisfiable"
                                                    _    -> putStrLn "... is not Satisfiable"

-- | Runs the main parsing unit (probably superfluous)
runLex :: (Eq a, Form a b c) => Parser (Boole a) -> String -> IO ()
runLex parser input = run (do spaces
                              res <- parser
                              eof
                              return res
                          ) input

{-
-- | Auxiliary run function for testing with the input given as string
runTest :: [Int] -> String -> IO ()
runTest ml input = do
    let h = head ml; t = tail ml
    in case h of
      1 -> runLex ((par5er Sqr parseKindex) :: Parser (L K)) input
      2 -> runLex ((par5er Sqr parseKDindex) :: Parser (L KD)) input
      3 -> runLex ((par5er Sqr parseCindex) :: Parser (L C)) input
      4 -> runLex ((par5er Ang parseGindex) :: Parser (L G)) input
      5 -> runLex ((par5er Ang parsePindex) :: Parser (L P)) input
      6 -> runLex ((par5er Sqr parseHMindex) :: Parser (L HM)) input
      7 -> runLex ((par5er Sqr parseMindex) :: Parser (L Mon)) input
      _ -> showHelp
    return ()
-}

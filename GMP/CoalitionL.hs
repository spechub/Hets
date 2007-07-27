{-# OPTIONS -fglasgow-exts #-}
module GMP.CoalitionL where

import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import GMP.GMPAS
import GMP.ModalLogic
import GMP.Lexer

data CLrules = CLrules ()

instance ModalLogic CL CLrules where
--    orderIns _ = True
    flagML _ = None
    parseIndex = do char '{'
                    let stopParser =  do try(char ',')
                                         return 0
                                  <|> do try(char '}')
                                         return (1::Integer)
                    let xParser s = do n <- natural
                                       let news = Set.insert (fromInteger n) s
                                       q <- stopParser
                                       case q of
                                         0 -> xParser news
                                         _ -> return news
                    let isEmptyParser =  do try(char '}')
                                            return Set.empty
                                     <|> do aux <- xParser Set.empty
                                            return aux
                    res <- isEmptyParser
                    return $ CL res
    matchR _ = [CLrules ()]
    guessClause r = case r of
                        _ -> []
-------------------------------------------------------------------------------

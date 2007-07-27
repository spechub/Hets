{-# OPTIONS -fglasgow-exts #-}
module GMP.CoalitionL where

import qualified Data.Set as Set
import GMP.GMPAS
import GMP.ModalLogic
import GMP.Lexer
{-
import qualified Data.Bits as Bits
import Text.ParserCombinators.Parsec
-}
data CLrules = CLrules ()

instance ModalLogic CL CLrules where
--    orderIns _ = True
    flagML _ = None
{-
    parseIndex = do (CL rres,size) <- bitParse 0
                    ;let res = revbInt rres size
                    ;return (CL res)
-}
    parseIndex = do char '{'
                    let stopParser =  do try(char ',')
                                         return 0
                                  <|> do try(char '}')
                                         return 1
                    let auxParser s = do n <- natural
                                         news = Set.insert n s
                                         q <- stopParser
                                         case q of
                                           0 -> auxParser news
                                           _ -> return news
                    return $ CL auxParser Set.empty
    matchR _ = [CLrules ()]
    guessClause r = case r of
                        _ -> []
{-
-- Bit-String parsing ---------------------------------------------------------
{-
 - @ param k :
 - @ param s :
 - @ return : -}
revbInt :: Integer -> Int -> Integer
revbInt k s = 
  let revaux x size y i = if (i == (size+1))
                          then 0
                          else let auxy = revaux x size y (i+1)
                                 in if (Bits.testBit x i)
                                    then Bits.setBit auxy (size-i)
                                    else Bits.clearBit auxy (size-i)
  in revaux k s (0::Int) (0::Int)
{- 
 - @ param i : 
 - @ return : -}
bitParse :: Int -> GenParser Char st (CL, Int)
bitParse i =  do try(char '0')
                 (CL n, size) <- bitParse (i+1)
                 return (CL (Bits.clearBit n i), size)
          <|> do try(char '1')
                 (CL n, size) <- bitParse (i+1)
                 return (CL(Bits.setBit n i), size)
          <|> return ((CL 0), i-1)
          <?> "GMPParse.bitParse"
-------------------------------------------------------------------------------
-}

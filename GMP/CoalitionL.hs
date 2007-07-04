{-# OPTIONS -fglasgow-exts #-}
module CoalitionL where

import GMPAS
import ModalLogic
import qualified Data.Bits as Bits
import Text.ParserCombinators.Parsec

data CLrules = CLrules ()

instance ModalLogic CL CLrules where
    flagML _ = None
    parseIndex = do (CL rres,size) <- bitParse 0
                    ;let res = revbInt rres size
                    ;return (CL res)
    matchRO ro = if (length ro == 0)
                  then []
                  else [CLrules ()]
    guessClause r = case r of
                    _ -> []
-- Bit-String parsing ---------------------------------------------------------
revbInt :: Integer -> Int -> Integer
revbInt k s
    = let
        revaux (x,size,y,i)
            = if (i == (size+1))
                then 0
                else let auxy = revaux(x,size,y,i+1)
                        in if (Bits.testBit x i)
                            then Bits.setBit auxy (size-i)
                            else Bits.clearBit auxy (size-i)
      in revaux(k,s,0::Int,0::Int)
bitParse :: Int -> GenParser Char st (CL, Int)
bitParse i =  do try(char('0'))
                 ;(CL n, size) <- bitParse (i+1)
                 ;return((CL(Bits.clearBit n i), size))
          <|> do try(char('1'))
                 ;(CL n, size) <- bitParse (i+1)
                 ;return((CL(Bits.setBit n i), size))
          <|> return ((CL 0), i-1)
          <?> "GMPParse.bitParse"
-------------------------------------------------------------------------------

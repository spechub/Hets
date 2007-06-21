{-# OPTIONS -fglasgow-exts #-}
module CoalitionL where

import GMPAS
import ModalLogic
import qualified Data.Bits as Bits
import Text.ParserCombinators.Parsec

instance ModalLogic CL CLrules where
    parseIndex = do (CL rres,size) <- bitParse 0
                    ;let res = revbInt rres size
                    ;return (CL res)
    matchRO ro = []
-- Bit-String parsing ---------------------------------------------------------
revbInt x size
    = let
        revaux (x,size,y,i)
            = if (i == (size+1))
                then 0
                else let y = revaux(x,size,y,i+1)
                        in if (Bits.testBit x i)
                            then Bits.setBit y (size-i)
                            else Bits.clearBit y (size-i)
      in revaux(x,size,0,0)

bitParse i =  do try(char('0'))
                 ;(CL n, size) <- bitParse (i+1)
                 ;return((CL(Bits.clearBit n i), size))
          <|> do try(char('1'))
                 ;(CL n, size) <- bitParse (i+1)
                 ;return((CL(Bits.setBit n i), size))
          <|> return ((CL 0), i-1)
          <?> "GMPParse.bitParse"
-------------------------------------------------------------------------------

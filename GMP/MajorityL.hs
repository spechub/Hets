{-# OPTIONS -fglasgow-exts #-}
module GMP.MajorityL where

import GMP.ModalLogic
import GMP.GMPAS
import GMP.Lexer

data MLrules = MLR [Int] [Int]
  deriving Show

instance ModalLogic ML MLrules where

    flagML _ = None

    parseIndex = do n <- natural
                    return $ ML (fromInteger n)

    matchR _ = []
    
    guessClause _ = [] 

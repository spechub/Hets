{- |
Module      :  $Header$
Description :  A parser for logic definitions
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Parse ( parseLogicDef ) where

import Common.Lexer
import Common.Parsec
import Common.Token (casl_structured_reserved_words)
import Common.AnnoState
import Framework.SignCat
import Text.ParserCombinators.Parsec

-- keywords which cannot appear as signature,morphism, and pattern names
framKeys :: [String]
framKeys = casl_structured_reserved_words ++
  ["logic","meta","syntax","truth","signatures","models","proofs"] 

-- parses a logic definition
parseLogicDef :: String -> IO Sign
parseLogicDef str = do
  let res = runParser logicP (AnnoState [] ()) "" str
  case res of
       Right sig -> return sig
       Left e -> error $ show e

-- parser for logic definitions
logicP :: AParser st Sign
logicP = do asKey "logic"
            l  <- nameP
            asKey "="
            f  <- metaP
            sy <- syntaxP
            t  <- truthP 
            si <- signaturesP
            m  <- modelsP
            p  <- proofsP
            return $ Sign l f sy t si m p            

-- parsers for components           
metaP :: AParser st FRAM
metaP = do asKey "meta"
           framP

syntaxP :: AParser st SIG_NAME
syntaxP = do asKey "syntax"
             nameP

truthP :: AParser st MORPH_NAME
truthP = do asKey "truth"
            nameP

signaturesP :: AParser st PATTERN_NAME
signaturesP = do asKey "signatures"
                 nameP

modelsP :: AParser st MORPH_NAME
modelsP = do asKey "models"
             nameP

proofsP :: AParser st MORPH_NAME
proofsP = do asKey "proofs"
             nameP

-- parsers for data types
nameP :: AParser st NAME
nameP = pToken $ reserved framKeys scanAnyWords

framP :: AParser st FRAM
framP = do asKey "LF"
           return LF
        <|> 
        do asKey "Isabelle"
           return Isabelle
        <|> 
        do asKey "Maude"
           return Maude

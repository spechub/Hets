{- |
Module      :  $Header$
Description :  Analyze eprover Output
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  portable
-}

module SoftFOL.EProver(proof,axiomsOf) where

import Text.ParserCombinators.Parsec
import Common.Parsec
import SoftFOL.ParseTPTP (singleQuoted,form)
import SoftFOL.Sign (SPTerm(..))
import qualified Data.Set as Set
import Data.List (foldl')

data Role      = Axiom | Other deriving (Show,Eq)

data Inference = ProofOf String
   | File { fileName :: String, formulaName :: String }
   | Inference { rule :: String,
                 status :: String,
                 parents :: Set.Set String } deriving (Show,Eq)

data ProofStep = ProofStep {
 name :: String,
 role :: Role,
 formula :: SPTerm,
 inference :: Inference } | Empty deriving (Show,Eq)

whiteSpace :: Parser ()
whiteSpace = oneOf "\r\t\v\f " >> return ()

line :: Parser ProofStep
line = ((do
 string "cnf(" <|> string "fof("
 n <- tok
 r <- tok
 f <- many whiteSpace >> form
 char ','
 i <- pinference
 string ")."
 return $ ProofStep n (if r == "axiom" then Axiom else Other)
  f i) <|> commentOrEmptyLine) << eof

commentOrEmptyLine :: Parser ProofStep
commentOrEmptyLine = ((skipMany (char '#') >>
 manyTill anyChar (lookAhead eof))
 <|> (skipMany whiteSpace >> return "")) >> return Empty

tok :: Parser String
tok = skipMany whiteSpace >> many (noneOf ",")
       << char ',' << skipMany whiteSpace

pinference :: Parser Inference
pinference = skipMany whiteSpace >> (
 (do
   string "file("
   f <- singleQuoted
   char ','
   skipMany whiteSpace
   n <- manyTill anyChar (char ')')
   return $ File f n) <|>
 (do
   string "inference("
   r <- tok
   string "[status("
   s <- manyTill anyChar (char ')')
   skipMany whiteSpace >> string "]"
   skipMany whiteSpace >> string ","
   skipMany whiteSpace >> string "["
   ps <- sepBy (manyTill anyChar (lookAhead $ oneOf ",]")) (char ',')
   skipMany whiteSpace
   string "])"
   return $ Inference r s (Set.fromList ps)
 ) <|>
 (do
   n <- tok
   string "['proof']"
   return $ ProofOf n
 ))

proof :: [String] -> [ProofStep]
proof s =
  snd $ foldr (\s' (s,ps') -> case runParser line () "" s' of
       Right p' | p' /= Empty ->
        if Set.member (name p') s || ps' == []
        then (insertParents (inference p') s, p':ps')
        else (s,ps')
       _ -> (s,ps')) (Set.empty, []) s
 where
  insertParents :: Inference -> Set.Set String -> Set.Set String
  insertParents (ProofOf n) s          = Set.insert n s
  insertParents (File _ n) s           = Set.insert n s
  insertParents (Inference _ szs ps'') s = Set.union ps'' s

axiomsOf :: [ProofStep] -> [String]
axiomsOf ps = map (formulaName . inference) $ filter (\p -> role p == Axiom) ps

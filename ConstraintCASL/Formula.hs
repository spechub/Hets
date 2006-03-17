{- |
Module      :  $Header$
Copyright   :  (c) Florian Mossakowski, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  fmossa@tzi.de
Stability   :  provisional
Portability :  portable

parse terms and formulae
-}

module ConstraintCASL.Formula     where

import Debug.Trace
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import ConstraintCASL.AS_ConstraintCASL
import Text.ParserCombinators.Parsec
import CASL.AS_Basic_CASL
import CASL.Formula
import Syntax.Parse_AS_Structured

-- ------------------------------------------------------------------------
-- formula
-- ------------------------------------------------------------------------

cformula :: [String] -> AParser st ConstraintFORMULA
cformula k = 
    --  trace ("parsing formula! " ++ show(k)) $
    try(
    do  c1 <- conjunction k	     
        impliesT
        c2 <- conjunction k 	 
        return (Implication_ConstraintFormula c1 c2))
  <|> 
    try(
    do c1 <- conjunction k 
       equivalentT
       c2 <-  trace ("conjucntion1: "++show (c1)) $ conjunction k 
       return (Equivalence_ConstraintFormula c1 c2)) 
  <|> 
    do impliesT 
       c <- conjunction k
       return (Axiom_ConstraintFormula c)

conjunction :: [String] -> AParser st ATOMCONJUNCTION
conjunction k = 
  --  trace ("parsing conjucntion! ") $
    do (atoms,_) <- atom k `separatedBy` anComma  
       return (Atom_Conjunction atoms)

atom :: [String] -> AParser st ATOM
atom k =
   -- trace ("parsing atom! ") $
    try (do r <- relation k
            oParenT
            (terms,_) <- constraintterm k `separatedBy` anComma
            cParenT `notFollowedWith` (relation k) 
            return (Prefix_Atom r terms))
  <|>
    do t1 <- constraintterm k 
       r <- relation k
       t2 <- constraintterm k
       return (Infix_Atom t1 r t2)

simplerelation :: [String] -> AParser st RELATION
simplerelation k =
   --trace ("parsing simple relation! ") $   
    do emptyRelationT 
       return Empty_Relation 
   <|>
    do equalityRelationT 
       return Equal_Relation 
   <|>
    do oParenT 
       r <- relation k
       cParenT 
       return r 
   <|>
    do id <- parseId k 
       return (Id_Relation id) 
   <|> 
    do inverseT 
       r <- relation k 
       return (Inverse_Relation r)  

relation :: [String] -> AParser st RELATION
relation k = 
   -- trace ("parsing relation list! ") $   
    try ( do (rels,_) <- simplerelation k `separatedBy` anComma
             return (Relation_Disjunction rels))
   <|>
    do r <- simplerelation k
       return r
   
constraintterm :: [String] -> AParser st ConstraintTERM
constraintterm k =
   --  trace ("parsing constraintterm! ") $
    try(do id <-  parseId k 
           return (Atomar_Term id))
   <|>
    do id <- parseId k 
       oParenT
       (terms,_) <- constraintterm k `separatedBy` anComma
       cParenT
       return (Composite_Term id terms)  

formula :: [String] -> AParser st ConstraintCASLFORMULA
formula k =  do x <- cformula k
                return (ExtFORMULA x)

emptyRelation :: String
emptyRelation = "{}"

emptyRelationT :: GenParser Char st Token
emptyRelationT = pToken $ toKey emptyRelation

equalityRelation :: String
equalityRelation = "="

equalityRelationT :: GenParser Char st Token
equalityRelationT = pToken $ toKey equalityRelation

inverse :: String
inverse = "~"

inverseT :: GenParser Char st Token
inverseT = pToken $ toKey inverse

implies :: String
implies = "|-"

impliesT :: GenParser Char st Token
impliesT = pToken $ toKey implies

equivalent :: String
equivalent = "-||-"

equivalentT :: GenParser Char st Token
equivalentT = pToken $ toKey equivalent

constraintKeywords :: [String]
constraintKeywords = (equivalent:implies:[])

instance AParsable ConstraintFORMULA where
  aparser = cformula []


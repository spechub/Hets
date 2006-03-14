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
    do  c1 <- conjunction k
        impliesT
        c2 <- conjunction k 
        return (Implication_ConstraintFormula c1 c2)
  <|> 
    do c1 <- conjunction k 
       equivalentT
       c2 <- conjunction k 
       return (Equivalence_ConstraintFormula c1 c2) 
  <|> 
    do impliesT 
       c <- conjunction k
       return (Axiom_ConstraintFormula c)

conjunction :: [String] -> AParser st ATOMCONJUNCTION
conjunction k = 
    do {atoms <- many1 (atom k); return (Atom_Conjunction atoms)}

atom :: [String] -> AParser st ATOM
atom k =
    try (do r <- relation k
            oParenT
            terms <- many1 (constraintterm k)
            cParenT `notFollowedWith` (relation k)
            trace ("atom1: "++show (Prefix_Atom r terms)) $
             return (Prefix_Atom r terms))
  <|>
    do t1 <- constraintterm k 
       r <- trace ("atom2:"++show t1) $ relation k
       t2 <- constraintterm k
       return (Infix_Atom t1 r t2)

relation :: [String] -> AParser st RELATION
relation k =  
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
       return (Inverse_Relation r) -- <|>
    --do {rels <- many1 (relation k); return (Relation_Disjunction rels)}

constraintterm :: [String] -> AParser st ConstraintTERM
constraintterm k =
    do id <- parseId k 
       return (Atomar_Term id)
   <|>
    do id <- parseId k 
       terms <- many1 (constraintterm k)
       return Composite_Term id terms  

formula :: [String] -> AParser st ConstraintCASLFORMULA
formula k = do x <- cformula k
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

instance AParsable ConstraintFORMULA where
  aparser = cformula []


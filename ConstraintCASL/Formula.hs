{- |
Module      :  $Header$
Copyright   :  (c) Florian Mossakowski, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

parse terms and formulae
-}

module ConstraintCASL.Formula     where

import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.Token
import ConstraintCASL.AS_ConstraintCASL
import Text.ParserCombinators.Parsec
import CASL.AS_Basic_CASL

-- ------------------------------------------------------------------------
-- formula
-- ------------------------------------------------------------------------

cformula :: [String] -> AParser st ConstraintFORMULA
cformula k =
    try(
    do  c1 <- conjunction k
        impliesT
        c2 <- conjunction k
        return (Implication_ConstraintFormula c1 c2))
  <|>
    try(
    do c1 <- conjunction k
       equivalentT
       c2 <- conjunction k
       return (Equivalence_ConstraintFormula c1 c2))
  <|>
    do impliesT
       c <- conjunction k
       return (Axiom_ConstraintFormula c)

conjunction :: [String] -> AParser st ATOMCONJUNCTION
conjunction k =
    do (atoms,_) <- atom k `separatedBy` anComma
       return (Atom_Conjunction atoms)

atom :: [String] -> AParser st ATOM
atom k =
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
    do ide <- parseId k
       return (Id_Relation ide)
   <|>
    do inverseT
       r <- relation k
       return (Inverse_Relation r)

relation :: [String] -> AParser st RELATION
relation k =
    try ( do (rels,_) <- simplerelation k `separatedBy` anComma
             return (Relation_Disjunction rels))
   <|>
    do r <- simplerelation k
       return r

constraintterm :: [String] -> AParser st ConstraintTERM
constraintterm k =
    try(do ide <-  parseId k
           return (Atomar_Term ide))
   <|>
    do ide <- parseId k
       oParenT
       (terms,_) <- constraintterm k `separatedBy` anComma
       cParenT
       return (Composite_Term ide terms)

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

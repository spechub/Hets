{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_BASIC_DFOL where

import Common.Id as Id

type VARIABLE = Id.Token
type CONSTANT = Id.Token


-- grammar for signatures
data SIG = Sig_empty
         | Sig SIG (CONSTANT, TYPE)
           deriving (Show, Eq)

-- grammar for contexts 
data CONTEXT = Context_empty
             | Context CONTEXT (VARIABLE, TYPE)
               deriving (Show, Eq)

-- grammar for types 
data TYPE = Sort
          | Form
          | Univ TERM
          | Pi (VARIABLE, TYPE) TYPE
            deriving (Show, Eq)

-- grammar for terms
data TERM = Term_var VARIABLE
          | Term_appl TERM TERM
            deriving (Show, Eq)
               


--grammar for formulas
data FORMULA = True
             | False
             | Pred TERM 
             | Equality TERM TERM 
             | Negation FORMULA 
             | Conjunction [FORMULA]
             | Disjunction [FORMULA]
             | Implication FORMULA FORMULA
             | Equivalence FORMULA FORMULA
             | Forall VARIABLE TERM FORMULA
             | Exists VARIABLE TERM FORMULA
               deriving (Show, Eq)


-- a DFOL specification
data BASIC_SPEC = Basic_spec SIG [FORMULA] 
                  deriving Show

 


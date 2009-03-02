{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_BASIC_DFOL 
    (
      SIG (..)                 -- datatype for signatures
    , CONTEXT                  -- datatype for contexts
    , TYPE	               -- datatype for types
    , TERM                     -- datatype for terms
    , FORMULA (..)             -- datatype for formulas
    , BASIC_SPEC (..)          -- Basic Spec    
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils

type VARIABLE = Id.Token
type CONSTANT = Id.Token


-- grammar for signatures
data SIG = Sig [(CONSTANT, TYPE)]
           deriving (Show, Eq)

-- grammar for contexts 
data CONTEXT = Context [(VARIABLE, TYPE)]
               deriving (Show, Eq)

-- grammar for types 
data TYPE = Sort
          | Form
          | Univ TERM
          | Pi [(VARIABLE, TYPE)] TYPE
            deriving (Show, Eq)

-- grammar for terms
data TERM = Var VARIABLE
          | Appl TERM TERM
            deriving (Show, Eq)

			
--grammar for formulas
data FORMULA = True
             | False
             | Pred TERM 
             | Equality TYPE TERM TERM 
             | Negation FORMULA
             | Conjunction [FORMULA]
             | Disjunction [FORMULA]
             | Implication FORMULA FORMULA
             | Equivalence FORMULA FORMULA
             | Forall [(VARIABLE, TYPE)] TERM FORMULA
             | Exists [(VARIABLE, TYPE)] TERM FORMULA
               deriving (Show, Eq)


-- a DFOL specification
data BASIC_SPEC = Basic_spec SIG [FORMULA] 
                  deriving Show


-- pretty printing
{-instance Pretty FORMULA where
    pretty = printFormula
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty SIG where
    pretty = printSignature
instance Pretty CONTEXT where
    pretty = printContext
instance Pretty TYPE where
    pretty = printType
instance Pretty TERM where
    pretty = printTerm


-- pretty printing for basic specs
printBasicSpec :: BASIC_SPEC -> Doc
--printBasicSpec (Basic_spec sig axioms) = hsep $ pretty sig map pretty axioms

-- pretty printing for formulas
printFormula :: FORMULA -> Doc
printFormula (Negation f) = notDoc
                            <> lparen <> printFormula f <> rparen
printFormula (Conjunction xs) = parens $
                                sepByArbitrary andDoc
                                $ map printFormula xs
printFormula (Disjunction xs) = parens $
                                sepByArbitrary orDoc
                                $ map printFormula xs
printFormula (Implication x y) = parens $ printFormula x <>
                                 implies <> printFormula y
printFormula (Equivalence x y) = parens $ printFormula x <>
                                 equiv <> printFormula y
printFormula (True) = text "True"
printFormula (False) = text "False"
printFormula (Pred x) = printTerm x
printFormula (Equality _ x y) = parens $ printTerm x <>
                                equals <> printTerm y
printFormula (Forall xs) = parens $
                                sepByArbitrary andDoc
                                $ map printFormula xs 

			
-- pretty printing for terms
printTerm :: TERM -> Doc
--printTerm (Var var) = pretty var
--printTerm (Appl f a) = parens $ printTerm f <> printTerm a

-- pretty printing for types
printType :: TYPE -> Doc
--printType (Sort) = text "Sort"
--printType (Form) = text "Form"
--printType (Univ t) = text "Univ" <> parens $ printTerm t
--printType (Pi xs t) = text "Pi" <> map (\(v, t) -> pretty v <> text ":" <> pretty t <> ". ") xs <> pretty x 

-- pretty printing for contexts
printContext :: CONTEXT -> Doc
--printType (Context xs) = parens $ map (\(v, t) -> pretty v <> text ":" <> pretty t <> ".") xs)

 -- pretty printing for signatures
printSignature :: SIG -> Doc
--printSignature (Sig xs) = hsep $ map (\(c, t) -> pretty c <> text ":" <> pretty t) xs
-}

{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_DFOL 
    (
      SPEC (..)                -- datatype for specifications
    , SPEC_ITEM (..)           -- datatype for specification items  
    , CONTEXT (..)             -- datatype for contexts
    , TYPE (..) 	       -- datatype for types
    , TERM (..)                -- datatype for terms
    , FORMULA (..)             -- datatype for formulas    
    ) where

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.AnnoState

type NAME = Token

-- a DFOL specification
data SPEC = Spec [Annoted SPEC_ITEM] 
            deriving Show
			
data SPEC_ITEM = Decl NAME TYPE
               | Axiom FORMULA
                 deriving Show  			

data TYPE = Sort
          | Form
          | Univ TERM
          | Pi [(NAME, TYPE)] TYPE
            deriving (Show, Eq)

data TERM = Identifier NAME
          | Appl TERM [TERM]
            deriving (Show, Eq)

data CONTEXT = Context [(NAME, TYPE)]
               deriving (Show, Eq)
			
data FORMULA = T
             | F
             | Pred TERM 
             | Equality TERM TERM 
             | Negation FORMULA
             | Conjunction [FORMULA]
             | Disjunction [FORMULA]
             | Implication FORMULA FORMULA
             | Equivalence FORMULA FORMULA
             | Forall [(NAME, TYPE)] FORMULA
             | Exists [(NAME, TYPE)] FORMULA
               deriving (Show, Eq)


-- pretty printing
instance Pretty SPEC where
    pretty = printSpec
instance Pretty SPEC_ITEM where
    pretty = printSpecItem
instance Pretty TYPE where
    pretty = printType
instance Pretty TERM where
    pretty = printTerm
instance Pretty FORMULA where
    pretty = printFormula
instance Pretty CONTEXT where
    pretty = printContext

printSpec :: SPEC -> Doc
printSpec (Spec xs) = vcat $ map pretty xs

printSpecItem :: SPEC_ITEM -> Doc
printSpecItem (Decl n t) = pretty n <+> text "::" <+> pretty t
printSpecItem (Axiom f) = pretty f

printFormula :: FORMULA -> Doc
printFormula (Negation f) = notDoc <+> printFormula f
printFormula (Conjunction xs) = parens $ sepBy andDoc $ map printFormula xs
printFormula (Disjunction xs) = parens $ sepBy orDoc $ map printFormula xs                                
printFormula (Implication x y) = parens $ printFormula x <+> implies <+> printFormula y
printFormula (Equivalence x y) = parens $ printFormula x <+> equiv <+> printFormula y
printFormula (T) = text "True"
printFormula (F) = text "False"
printFormula (Pred x) = pretty x
printFormula (Equality x y) = parens $ pretty x <+> equals <+> pretty y
printFormula (Forall xs f) = parens $ forallDoc <+> (hsep $ map printVar xs) <+> printFormula f 
printFormula (Exists xs f) = parens $ exists <+> (hsep $ map printVar xs) <+> printFormula f
			
printTerm :: TERM -> Doc
printTerm (Identifier x) = pretty x
printTerm (Appl f xs) = parens $ pretty f <+> (hsep $ map pretty xs)

printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Pi xs x) = text "Pi" <+> (hsep $ map printVar xs) <+> printType x 

printContext :: CONTEXT -> Doc
printContext (Context xs) = parens $ hsep $ map printVar xs

-- auxiliary functions for printing
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ (x:[]) = x
sepBy separator (x:xs) = x <+> separator <+> (sepBy separator xs)

printVar :: (NAME, TYPE) -> Doc
printVar (n, t) = pretty n <+> text ":" <+> pretty t <> text "."

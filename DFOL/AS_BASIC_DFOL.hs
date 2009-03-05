{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_BASIC_DFOL 
    (
      SIG (..)                 -- datatype for signatures
    , CONTEXT (..)             -- datatype for contexts
    , TYPE (..) 	       -- datatype for types
    , TERM (..)                -- datatype for terms
    , FORMULA (..)             -- datatype for formulas
    , BASIC_SPEC (..)          -- Basic Spec    
    ) where

import Common.Id
import Common.Doc
import Common.DocUtils

type NAME = Token

-- grammar for signatures
data SIG = Sig [(NAME, TYPE)]
           deriving (Show, Eq)

-- grammar for contexts 
data CONTEXT = Context [(NAME, TYPE)]
               deriving (Show, Eq)

-- grammar for types 
data TYPE = Sort
          | Form
          | Univ TERM
          | Pi [(NAME, TYPE)] TYPE
            deriving (Show, Eq)

-- grammar for terms
data TERM = Identifier NAME
          | Appl TERM [TERM]
            deriving (Show, Eq)

--grammar for formulas
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

-- a DFOL specification
data BASIC_SPEC = Basic_spec SIG [FORMULA] 
                  deriving Show

-- pretty printing
instance Pretty FORMULA where
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
printBasicSpec (Basic_spec sig axioms) = (pretty sig) $+$ (vcat $ map pretty axioms)

-- pretty printing for formulas
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
printFormula (Forall xs f) = parens $ forallDoc <+> (hsep $ map printDecl xs) <+> printFormula f 
printFormula (Exists xs f) = parens $ exists <+> (hsep $ map printDecl xs) <+> printFormula f
			
-- pretty printing for terms
printTerm :: TERM -> Doc
printTerm (Identifier x) = pretty x
printTerm (Appl f xs) = parens $ pretty f <+> (hsep $ map pretty xs)

-- pretty printing for types
printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Pi xs x) = text "Pi" <+> (hsep $ map printDecl xs) <+> printType x 

-- pretty printing for contexts
printContext :: CONTEXT -> Doc
printContext (Context xs) = parens $ hsep $ map printDecl xs

-- pretty printing for signatures
printSignature :: SIG -> Doc
printSignature (Sig xs) = vcat $ map (\(c, t) -> pretty c <+> text "::" <+> pretty t) xs

-- auxiliary functions
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ (x:[]) = x
sepBy separator (x:xs) = x <+> separator
                           <+> (sepBy separator xs)

printDecl :: (NAME, TYPE) -> Doc
printDecl (n, t) = pretty n <+> text ":" <+> pretty t <> text "."

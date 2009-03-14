{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_DFOL
   {- (
      BASIC_SPEC (..)          -- datatype for specifications
    , BASIC_ITEM (..)          -- datatype for specification items
    , TYPE (..)                -- datatype for types
    , TERM (..)                -- datatype for terms
    , FORMULA (..)             -- datatype for formulas
    ) -} where

import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils

type NAME = Token

-- a DFOL specification
data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEM]
                  deriving Show

data BASIC_ITEM = Decl [NAME] TYPE
                | Axiom FORMULA
                  deriving Show

data TYPE = Sort
          | Form
          | Univ TERM
          | Pi [([NAME],TYPE)] TYPE
            deriving (Show, Eq)

data TERM = Identifier NAME
          | Appl TERM [TERM]
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
             | Forall [([NAME],TYPE)] FORMULA
             | Exists [([NAME],TYPE)] FORMULA
               deriving (Show, Eq)

-- pretty printing
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEM where
    pretty = printBasicItem
instance Pretty TYPE where
    pretty = printType
instance Pretty TERM where
    pretty = printTerm
instance Pretty FORMULA where
    pretty = printFormula

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl ns t) = printNames ns <+> text "::" <+> printType t
printBasicItem (Axiom f) = printFormula f

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

-- auxiliary functions for printing
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ [x] = x
sepBy separator (x:xs) = x <+> separator <+> sepBy separator xs

printNames :: [NAME] -> Doc
printNames [] = text ""
printNames [n] = pretty n
printNames (n:ns) = pretty n <> comma <+> printNames ns

printVar :: ([NAME], TYPE) -> Doc
printVar (ns, t) = printNames ns <+> colon <+> pretty t <> dot  

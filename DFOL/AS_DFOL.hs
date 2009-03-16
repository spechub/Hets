{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_DFOL where

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
printBasicItem (Axiom f) = text "axiom" <+> printFormula f

printFormula :: FORMULA -> Doc
printFormula (Negation f) = notDoc <+> (parens $ printFormula f)
printFormula (Conjunction xs) = sepBy (text " /\\ ") $ map parens $ map printFormula xs
printFormula (Disjunction xs) = sepBy (text " \\/ ") $ map parens $ map printFormula xs
printFormula (Implication x y) = (parens $ printFormula x) <+> implies <+> (parens $ printFormula y)
printFormula (Equivalence x y) = (parens $ printFormula x) <+> equiv <+> (parens $ printFormula y)
printFormula (T) = text "true"
printFormula (F) = text "false"
printFormula (Pred x) = pretty x
printFormula (Equality x y) = pretty x <+> equals <+> pretty y
printFormula (Forall xs f) = forallDoc <+> (hsep $ map printVar xs) <+> printFormula f
printFormula (Exists xs f) = exists <+> (hsep $ map printVar xs) <+> printFormula f

printTerm :: TERM -> Doc
printTerm t = pretty f 
              <> 
              if as /= [] 
                 then (parens $ sepBy (text ", ") $ map pretty as) 
                 else text "" 
              where 
              f = fst $ termCanForm t
              as = snd $ termCanForm t  

printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = text "Univ" <+> pretty t
printType (Pi xs x) = text "Pi" <+> (hsep $ map printVar xs) <+> printType x

-- auxiliary functions for printing
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ [x] = x
sepBy separator (x:xs) = x <> separator <> sepBy separator xs

printNames :: [NAME] -> Doc
printNames ns = sepBy (text ", ") $ map pretty ns

printVar :: ([NAME], TYPE) -> Doc
printVar (ns, (Univ t)) = printNames ns <+> colon <+> printTerm t <> dot  

termCanForm :: TERM -> (NAME, [TERM])
termCanForm (Identifier t) = (t, [])
termCanForm (Appl f args) = (fst $ termCanForm f, (snd $ termCanForm f) ++ args)




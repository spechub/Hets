{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
-}

module DFOL.AS_DFOL where

import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils
import DFOL.Utils

type NAME = Token

-- grammar for basic specification
data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEM]
                  deriving Show

data BASIC_ITEM = Decl [NAME] TYPE
                | Axiom FORMULA
                  deriving Show

data TYPE = Sort
          | Form
          | Univ TERM
          | Func [TYPE]
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

-- grammar for symbols and symbol maps
type SYMB = NAME

data SYMB_ITEMS = Symb_items [SYMB]
                  deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP]
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB               
                   deriving (Show, Eq)   

-- converts a term into its canonical form f(x_1, ... x_n)
termCanForm :: TERM -> (NAME, [TERM])
termCanForm (Identifier t) = (t, [])
termCanForm (Appl f args) = (fst $ termCanForm f, (snd $ termCanForm f) ++ args)

-- determines the precedence of a formula
formulaPrec :: FORMULA -> Int
formulaPrec T = truePrec
formulaPrec F = falsePrec
formulaPrec Pred {} = predPrec
formulaPrec Equality {} = equalPrec
formulaPrec Negation {} = negPrec
formulaPrec Disjunction {} = disjPrec
formulaPrec Conjunction {} = conjPrec
formulaPrec Implication {} = implPrec
formulaPrec Equivalence {} = equivPrec
formulaPrec Forall {} = forallPrec
formulaPrec Exists {} = existsPrec

-- determines the precedence of a type
typePrec :: TYPE -> Int
typePrec Sort = sortPrec
typePrec Form = formPrec
typePrec Univ {} = univPrec
typePrec Func {} = funcPrec
typePrec Pi {} = piPrec

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
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap

-- print basic specifications
printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

-- print basic items
printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl ns t) = printNames ns <+> text "::" <+> printType t
printBasicItem (Axiom f) = dot <> printFormula f

-- print types
printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Func ts) = sepBy (text " -> ") $ map (printSubType funcPrec) ts
printType (Pi xs x) = text "Pi" <+> printVars xs <+> printType x

printSubType :: Int -> TYPE -> Doc
printSubType prec t = if (typePrec t) >= prec
                         then parens $ printType t
                         else printType t  
-- print terms
printTerm :: TERM -> Doc
printTerm t = pretty f 
              <> 
              if as == [] 
                 then text ""
                 else (parens $ sepBy (text ", ") $ map pretty as) 
              where 
              f = fst $ termCanForm t
              as = snd $ termCanForm t  

-- print formulas
printFormula :: FORMULA -> Doc
printFormula (T) = text "true"
printFormula (F) = text "false"
printFormula (Pred x) = pretty x
printFormula (Equality x y) = pretty x <+> text "==" <+> pretty y
printFormula (Negation f) = notDoc <+> printSubFormula negPrec f
printFormula (Conjunction xs) = sepBy (text " /\\ ") $ map (printSubFormula conjPrec) xs
printFormula (Disjunction xs) = sepBy (text " \\/ ") $ map (printSubFormula disjPrec) xs
printFormula (Implication x y) = printSubFormula implPrec x <+> implies <+> printSubFormula implPrec y
printFormula (Equivalence x y) = printSubFormula equivPrec x <+> equiv <+> printSubFormula equivPrec y
printFormula (Forall xs f) = forallDoc <+> printVars xs <+> printFormula f
printFormula (Exists xs f) = exists <+> printVars xs <+> printFormula f

printSubFormula :: Int -> FORMULA -> Doc
printSubFormula prec f = if (formulaPrec f) > prec
                            then parens $ printFormula f
                            else printFormula f  

-- print symbol items
printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs) = sepBy (text ", ") $ map pretty xs

-- print symbol map items
printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs) = sepBy (text ", ") $ map pretty xs

-- print symbol or map
printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb s) = pretty s
printSymbOrMap (Symb_map s t) = pretty s <+> mapsto <+> pretty t  

-- auxiliary functions for printing
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ [x] = x
sepBy separator (x:xs) = x <> separator <> sepBy separator xs

printNames :: [NAME] -> Doc
printNames ns = sepBy (text ", ") $ map pretty ns

printVar :: ([NAME], TYPE) -> Doc
printVar (ns, t) = printNames ns <+> colon <+> printType t

printVars :: [([NAME], TYPE)] -> Doc  
printVars xs = (sepBy (text "; ") $ map printVar xs) <> dot   



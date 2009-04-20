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
type DECL = ([NAME],TYPE)

-- grammar for basic specification
data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEM]
                  deriving Show

data BASIC_ITEM = Decl_item DECL
                | Axiom_item FORMULA
                  deriving Show

data TYPE = Sort
          | Form
          | Univ TERM
          | Func [TYPE] TYPE
          | Pi [DECL] TYPE
            deriving (Show, Ord, Eq)

data TERM = Identifier NAME
          | Appl TERM [TERM]
            deriving (Show, Ord, Eq)

data FORMULA = T
             | F
             | Pred TERM
             | Equality TERM TERM
             | Negation FORMULA
             | Conjunction [FORMULA]
             | Disjunction [FORMULA]
             | Implication FORMULA FORMULA
             | Equivalence FORMULA FORMULA
             | Forall [DECL] FORMULA
             | Exists [DECL] FORMULA
               deriving (Show, Ord, Eq)

-- grammar for symbols and symbol maps
type SYMB = NAME

data SYMB_ITEMS = Symb_items [SYMB]
                  deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP]
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB
                   deriving (Show, Eq)

-- converts a term into a form where a function is applied to exactly one argument
termApplForm :: TERM -> TERM
termApplForm (Identifier t) = Identifier t
termApplForm (Appl f []) = termApplForm f
termApplForm (Appl f [a]) = Appl (termApplForm f) [a]
termApplForm (Appl f as) = Appl (termApplForm $ Appl f $ init as) $ [last as]

-- determines the canonical form of a term, i.e. the function symbol applied and the argument list
termCanForm :: TERM -> (NAME, [TERM])
termCanForm (Identifier x) = (x,[])
termCanForm (Appl f as) = (x, bs ++ as)
                          where (x,bs) = termCanForm f

-- precedences - needed for pretty printing
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

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl_item (ns,t)) = printNames ns <+> text "::" <+> printType t
printBasicItem (Axiom_item f) = dot <> printFormula f

printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Func ts t) = fsep $ prepPunctuate (text "-> ") $ map (printSubType funcPrec) (ts ++ [t])
printType (Pi xs x) = text "Pi" <+> printDecls xs <+> printType x

printSubType :: Int -> TYPE -> Doc
printSubType prec t = if typePrec t >= prec
                         then parens $ printType t
                         else printType t

printTerm :: TERM -> Doc
printTerm t = if (as == [])
                 then pretty x
                 else pretty x <> parens (ppWithCommas as)
              where (x,as) = termCanForm t

printFormula :: FORMULA -> Doc
printFormula (T) = text "true"
printFormula (F) = text "false"
printFormula (Pred x) = pretty x
printFormula (Equality x y) = pretty x <+> text "==" <+> pretty y
printFormula (Negation f) = notDoc <+> printSubFormula negPrec f
printFormula (Conjunction xs) = fsep $ prepPunctuate (andDoc <> space)
  $ map (printSubFormula conjPrec) xs
printFormula (Disjunction xs) = fsep $ prepPunctuate (orDoc <> space)
  $ map (printSubFormula disjPrec) xs
printFormula (Implication x y) = printSubFormula implPrec x <+> implies
  <+> printSubFormula implPrec y
printFormula (Equivalence x y) = printSubFormula equivPrec x <+> equiv
  <+> printSubFormula equivPrec y
printFormula (Forall xs f) = forallDoc <+> printDecls xs <+> printFormula f
printFormula (Exists xs f) = exists <+> printDecls xs <+> printFormula f

printSubFormula :: Int -> FORMULA -> Doc
printSubFormula prec f = if (formulaPrec f) > prec
                            then parens $ printFormula f
                            else printFormula f

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs) = ppWithCommas xs

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs) = ppWithCommas xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb s) = pretty s
printSymbOrMap (Symb_map s t) = pretty s <+> mapsto <+> pretty t

printNames :: [NAME] -> Doc
printNames = ppWithCommas

printDecl :: DECL -> Doc
printDecl (ns, t) = printNames ns <+> colon <+> printType t

printDecls :: [DECL] -> Doc
printDecls xs = fsep (punctuate semi $ map printDecl xs) <> dot

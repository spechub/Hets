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
import Data.List
import qualified Data.Set as Set

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
          | Func [TYPE]
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

-- operations on a list of declarations
getVarsFromDecls :: [DECL] -> Set.Set NAME
getVarsFromDecls ds = Set.unions $ map Set.fromList $ map fst ds 

getTypeFromDecls :: NAME -> [DECL] -> Maybe TYPE
getTypeFromDecls n ds = case result of
                             Just (_,t) -> Just t  
                             Nothing -> Nothing             
                        where result = find (\(ns,_) -> elem n ns) ds

-- converts a term into its canonical form f(x_1, ... x_n)
termCanForm :: TERM -> TERM
termCanForm (Identifier t) = (Identifier t)
termCanForm (Appl f as) = case termF of
                               Identifier _ -> (Appl f as)
                               Appl g bs -> (Appl g (bs ++ as))   
                          where termF = termCanForm f    

-- converts a term into a form where a function is applied to exactly one argument
termApplForm :: TERM -> TERM
termApplForm (Identifier t) = Identifier t
termApplForm (Appl f []) = termApplForm f
termApplForm (Appl f [a]) = Appl (termApplForm f) [a]
termApplForm (Appl f as) = Appl (termApplForm $ Appl f $ init as) $ [last as]

-- substitutions
substituteTermInType :: NAME -> TERM -> TYPE -> TYPE
substituteTermInType _ _ Sort = Sort
substituteTermInType _ _ Form = Form
substituteTermInType n val (Univ t) = Univ $ substituteTermInTerm n val t
substituteTermInType n val (Func ts) = Func $ map (substituteTermInType n val) ts
substituteTermInType n val (Pi ds t) = Pi (substituteTermInDecls n val ds) (substituteTermInType n val t)   

substituteTermInTerm :: NAME -> TERM -> TERM -> TERM
substituteTermInTerm n val (Identifier x) = if (x == n) then val else Identifier x
substituteTermInTerm n val (Appl f as) = Appl (substituteTermInTerm n val f) $ map (substituteTermInTerm n val) as 

substituteTermInDecls :: NAME -> TERM -> [DECL] -> [DECL] 
substituteTermInDecls n val ds = map (substituteTermInDecl n val) ds

substituteTermInDecl :: NAME -> TERM -> DECL -> DECL 
substituteTermInDecl n val (ns,t) = (ns, substituteTermInType n val t)

substituteVarInType :: NAME -> NAME -> TYPE -> TYPE
substituteVarInType _ _ Sort = Sort
substituteVarInType _ _ Form = Form
substituteVarInType n1 n2 (Univ t) = Univ $ substituteVarInTerm n1 n2 t
substituteVarInType n1 n2 (Func ts) = Func $ map (substituteVarInType n1 n2) ts
substituteVarInType n1 n2 (Pi ds t) = Pi (substituteVarInDecls n1 n2 ds) (substituteVarInType n1 n2 t)   

substituteVarInTerm :: NAME -> NAME -> TERM -> TERM
substituteVarInTerm n1 n2 (Identifier x) = if (x == n1) then Identifier n2 else Identifier x
substituteVarInTerm n1 n2 (Appl f as) = Appl (substituteVarInTerm n1 n2 f) $ map (substituteVarInTerm n1 n2) as 

substituteVarInDecls :: NAME -> NAME -> [DECL] -> [DECL] 
substituteVarInDecls n1 n2 ds = map (substituteVarInDecl n1 n2) ds

substituteVarInDecl :: NAME -> NAME -> DECL -> DECL 
substituteVarInDecl n1 n2 (ns,t) = (substituteVarInNames n1 n2 ns, substituteVarInType n1 n2 t)

substituteVarInNames :: NAME -> NAME -> [NAME] -> [NAME] 
substituteVarInNames n1 n2 ns = map (\n -> if n == n1 then n2 else n) ns

-- returns a list of declared variables from within a type
getVarsInType :: TYPE -> Set.Set NAME
getVarsInType (Pi ds t) = Set.union (getVarsFromDecls ds) (getVarsInType t)
getVarsInType _ = Set.empty

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
instance Pretty [NAME] where
    pretty = printNames
instance Pretty DECL where
    pretty = printDecl
instance Pretty [DECL] where
    pretty = printDecls

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl_item (ns,t)) = printNames ns <+> text "::" <+> printType t
printBasicItem (Axiom_item f) = dot <> printFormula f

printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Func ts) = sepBy (text " -> ") $ map (printSubType funcPrec) ts
printType (Pi xs x) = text "Pi" <+> printDecls xs <+> printType x

printSubType :: Int -> TYPE -> Doc
printSubType prec t = if (typePrec t) >= prec
                         then parens $ printType t
                         else printType t
printTerm :: TERM -> Doc
printTerm t = printTermCanForm $ termCanForm t

printTermCanForm :: TERM -> Doc
printTermCanForm (Identifier x) = pretty x
printTermCanForm (Appl f as) = pretty f <> (parens $ sepBy (text ", ") $ map pretty as)                  

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
printFormula (Forall xs f) = forallDoc <+> printDecls xs <+> printFormula f
printFormula (Exists xs f) = exists <+> printDecls xs <+> printFormula f

printSubFormula :: Int -> FORMULA -> Doc
printSubFormula prec f = if (formulaPrec f) > prec
                            then parens $ printFormula f
                            else printFormula f

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs) = sepBy (text ", ") $ map pretty xs

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs) = sepBy (text ", ") $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb s) = pretty s
printSymbOrMap (Symb_map s t) = pretty s <+> mapsto <+> pretty t

printNames :: [NAME] -> Doc
printNames ns = sepBy (text ", ") $ map pretty ns

printDecl :: DECL -> Doc
printDecl (ns, t) = printNames ns <+> colon <+> printType t

printDecls :: [DECL] -> Doc
printDecls xs = (sepBy (text "; ") $ map printDecl xs) <> dot

-- auxiliary functions for printing
sepBy :: Doc -> [Doc] -> Doc
sepBy _ [] = text ""
sepBy _ [x] = x
sepBy separator (x:xs) = x <> separator <> sepBy separator xs

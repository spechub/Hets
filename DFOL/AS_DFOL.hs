{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module DFOL.AS_DFOL
   (  NAME,
      DECL,
      BASIC_SPEC (..),
      BASIC_ITEM (..),
      TYPE (..),
      TERM (..),
      FORMULA (..),
      SYMB,
      SYMB_ITEMS (..),
      SYMB_MAP_ITEMS (..),
      SYMB_OR_MAP (..),
      termRecForm,
      termFlatForm,
      typeRecForm,
      typeFlatForm,
      formulaRecForm,
      formulaFlatForm,
      printNames,
      printDecls,
      getVarsFromDecls,
      getVarTypeFromDecls,
      compactDecls,
      expandDecls,
      Translatable,
      translate,
      getNewName,
      getFreeVars
   )  where

import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils
import DFOL.Utils
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

type NAME = Token
type DECL = ([NAME],TYPE)

-- grammar for basic specification
data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEM]
                  deriving Show

instance GetRange BASIC_SPEC

data BASIC_ITEM = Decl_item DECL
                | Axiom_item FORMULA
                  deriving Show

data TYPE = Sort
          | Form
          | Univ TERM
          | Func [TYPE] TYPE
          | Pi [DECL] TYPE
            deriving (Show, Ord)

data TERM = Identifier NAME
          | Appl TERM [TERM]
            deriving (Show, Ord)

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

instance GetRange FORMULA

-- grammar for symbols and symbol maps
type SYMB = NAME

data SYMB_ITEMS = Symb_items [SYMB]
                  deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP]
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB
                   deriving (Show, Eq)

-- canonical forms

{- converts a term into a form where a function is applied to
   exactly one argument -}
termRecForm :: TERM -> TERM
termRecForm (Identifier t) = Identifier t
termRecForm (Appl f []) = termRecForm f
termRecForm (Appl f as) = 
  Appl (termRecForm $ Appl f $ init as) $ [termRecForm $ last as]

{- converts a type into a form where each construct takes
   exactly one argument -}
typeRecForm :: TYPE -> TYPE
typeRecForm (Func [] a) = typeRecForm a
typeRecForm (Func (t:ts) a) = Func [typeRecForm t] $ typeRecForm $ Func ts a
typeRecForm (Pi [] t) = typeRecForm t
typeRecForm (Pi (([],_):ds) a) = typeRecForm $ Pi ds a
typeRecForm (Pi (((n:ns),t):ds) a) =
  Pi [([n],typeRecForm t)] $ typeRecForm $ Pi ((ns,t):ds) a
typeRecForm t = t

{- converts a formula into a form where each quantifier takes
   exactly one argument -}
formulaRecForm :: FORMULA -> FORMULA
formulaRecForm (Negation f) = formulaRecForm f
formulaRecForm (Conjunction fs) = Conjunction $ map formulaRecForm fs
formulaRecForm (Disjunction fs) = Disjunction $ map formulaRecForm fs
formulaRecForm (Implication f g) = 
  Implication (formulaRecForm f) (formulaRecForm g)
formulaRecForm (Equivalence f g) = 
  Equivalence (formulaRecForm f) (formulaRecForm g)
formulaRecForm (Forall [] f) = formulaRecForm f
formulaRecForm (Forall (([],_):ds) f) = formulaRecForm $ Forall ds f
formulaRecForm (Forall (((n:ns),t):ds) f) =
  Forall [([n],t)] $ formulaRecForm $ Forall ((ns,t):ds) f
formulaRecForm (Exists [] f) = formulaRecForm f
formulaRecForm (Exists (([],_):ds) f) = formulaRecForm $ Exists ds f
formulaRecForm (Exists (((n:ns),t):ds) f) =
  Exists [([n],t)] $ formulaRecForm $ Exists ((ns,t):ds) f
formulaRecForm t = t

{- determines the flattened form of a term, i.e. the function symbol
   applied and the argument list -}
termFlatForm :: TERM -> (NAME, [TERM])
termFlatForm (Identifier x) = (x,[])
termFlatForm (Appl f as) = (x, bs ++ as)
                          where (x,bs) = termFlatForm f

{- converts a type into a flattened form where each operator binds maximum
   number of arguments -}
typeFlatForm :: TYPE -> TYPE
typeFlatForm (Func [] t) = typeFlatForm t
typeFlatForm (Func ts t) = 
  let ts1 = map typeFlatForm ts
      t1 = typeFlatForm t
      in case t1 of
         Func ts2 t2 -> Func (ts1 ++ ts2) t2
         _ -> Func ts1 t1
typeFlatForm (Pi [] t) = typeFlatForm t
typeFlatForm (Pi ds t) =
  let ds1 = map (\ (ns,t3) -> (ns,typeFlatForm t3)) ds
      t1 = typeFlatForm t
      in case t1 of
         Pi ds2 t2 -> Pi (compactDecls (ds1 ++ ds2)) t2
         _ -> Pi (compactDecls ds1) t1
typeFlatForm t = t

{- converts a formula into a flattened form where each quantifier binds maximum
   number of arguments -}
formulaFlatForm :: FORMULA -> FORMULA
formulaFlatForm (Negation f) = formulaFlatForm f
formulaFlatForm (Conjunction []) = T
formulaFlatForm (Conjunction fs) = Conjunction $ map formulaFlatForm fs
formulaFlatForm (Disjunction []) = F
formulaFlatForm (Disjunction fs) = Disjunction $ map formulaFlatForm fs
formulaFlatForm (Implication f g) = 
  Implication (formulaFlatForm f) (formulaFlatForm g)
formulaFlatForm (Equivalence f g) = 
  Equivalence (formulaFlatForm f) (formulaFlatForm g)
formulaFlatForm (Forall [] f) = formulaFlatForm f
formulaFlatForm (Forall ds1 f) =
  let f1 = formulaFlatForm f
      in case f1 of
         Forall ds2 f2 -> Forall (compactDecls (ds1 ++ ds2)) f2
         _ -> Forall (compactDecls ds1) f1
formulaFlatForm (Exists [] f) = formulaFlatForm f
formulaFlatForm (Exists ds1 f) =
  let f1 = formulaFlatForm f
      in case f1 of
         Exists ds2 f2 -> Exists (compactDecls (ds1 ++ ds2)) f2
         _ -> Exists (compactDecls ds1) f1
formulaFlatForm t = t

-- substitutions

{- class of types containing identifiers which may be
   substituted by terms -}
class Translatable a where
   {- substitutions and renamings: the first argument specifies the desired
      term/identifier substitutions and the second the set of identifiers which
      cannot be used as new variable names -}
   translate :: Map.Map NAME TERM -> Set.Set NAME -> a -> a

instance Translatable TERM where
   translate m _ = (translateTerm m) . termRecForm
instance Translatable TYPE where
   translate m s = (translateType m s) . typeRecForm
instance Translatable FORMULA where
   translate m s = (translateFormula m s) . formulaRecForm

translateTerm :: Map.Map NAME TERM -> TERM -> TERM
translateTerm m (Identifier x) = Map.findWithDefault (Identifier x) x m
translateTerm m (Appl f [a]) = Appl (translateTerm m f) [translateTerm m a]
translateTerm _ t = t

translateType :: Map.Map NAME TERM -> Set.Set NAME -> TYPE -> TYPE
translateType _ _ Sort = Sort
translateType _ _ Form = Form
translateType m s (Univ t) = Univ $ translate m s t
translateType m s (Func ts t) = Func (map (translate m s) ts) (translate m s t)
translateType m s (Pi [([x],t)] a) =
  let t1 = translate m s t
      x1 = getNewName x s
      a1 = translate (Map.insert x (Identifier x1) m) (Set.insert x1 s) a
      in Pi [([x1],t1)] a1
translateType _ _ t = t

translateFormula :: Map.Map NAME TERM -> Set.Set NAME -> FORMULA -> FORMULA
translateFormula _ _ T = T
translateFormula _ _ F = F
translateFormula m s (Pred t) = Pred $ translate m s t
translateFormula m s (Equality t1 t2) =
  Equality (translate m s t1) (translate m s t2)
translateFormula m s (Negation f) = Negation $ translate m s f
translateFormula m s (Conjunction fs) =
  Conjunction $ map (translate m s) fs
translateFormula m s (Disjunction fs) =
  Disjunction $ map (translate m s) fs
translateFormula m s (Implication f g) =
  Implication (translate m s f) (translate m s g)
translateFormula m s (Equivalence f g) =
  Equivalence (translate m s f) (translate m s g)
translateFormula m s (Forall [([x],t)] f) =
  let t1 = translate m s t
      x1 = getNewName x s
      f1 = translate (Map.insert x (Identifier x1) m) (Set.insert x1 s) f
      in Forall [([x1],t1)] f1
translateFormula m s (Exists [([x],t)] f) =
  let t1 = translate m s t
      x1 = getNewName x s
      f1 = translate (Map.insert x (Identifier x1) m) (Set.insert x1 s) f
      in Exists [([x1],t1)] f1
translateFormula _ _ f = f

{- modifies the given name until it is different from each of the names
   in the input set -}
getNewName :: NAME -> Set.Set NAME -> NAME
getNewName var names = getNewNameH var names (tokStr var) 0

getNewNameH :: NAME -> Set.Set NAME -> String -> Int -> Token
getNewNameH var names root i =
  if (Set.notMember var names)
     then var
     else let newVar = Token (root ++ (show i)) nullRange
              in getNewNameH newVar names root $ i+1

-- equality
instance Eq TERM where
    u == v = eqTerm (termRecForm u) (termRecForm v)
instance Eq TYPE where
    u == v = eqType (typeRecForm u) (typeRecForm v)

eqTerm :: TERM -> TERM -> Bool
eqTerm (Identifier x1) (Identifier x2) = x1 == x2
eqTerm (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2]
eqTerm _ _ = False

eqType :: TYPE -> TYPE -> Bool
eqType Sort Sort = True
eqType Form Form = True
eqType (Univ t1) (Univ t2) = t1 == t2
eqType (Func [t1] s1) (Func [t2] s2) = and [t1 == t2, s1 == s2]
eqType (Pi [([n1],t1)] s1) (Pi [([n2],t2)] s2) =
  let syms1 = Set.delete n1 $ getFreeVars $ typeRecForm s1
      syms2 = Set.delete n2 $ getFreeVars $ typeRecForm s2
      v = getNewName n1 $ Set.union syms1 syms2
      type1 = translate (Map.singleton n1 (Identifier v)) syms1 s1
      type2 = translate (Map.singleton n2 (Identifier v)) syms2 s2
      in and [t1 == t2, type1 == type2]  
eqType _ _ = False

-- returns a set of unbound identifiers used within a type
getFreeVars :: TYPE -> Set.Set NAME
getFreeVars e = getFreeVarsH $ typeRecForm e

getFreeVarsH :: TYPE -> Set.Set NAME
getFreeVarsH Sort = Set.empty
getFreeVarsH Form = Set.empty
getFreeVarsH (Univ t) = getFreeVarsInTerm t
getFreeVarsH (Func [t] v) =  
  Set.union (getFreeVarsH t) (getFreeVarsH v)
getFreeVarsH (Pi [([n],t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH _ = Set.empty

getFreeVarsInTerm :: TERM -> Set.Set NAME
getFreeVarsInTerm t = getFreeVarsInTermH $ termRecForm t

getFreeVarsInTermH :: TERM -> Set.Set NAME
getFreeVarsInTermH (Identifier x) = Set.singleton x
getFreeVarsInTermH (Appl f [a]) =
  Set.union (getFreeVarsInTermH f) (getFreeVarsInTermH a)
getFreeVarsInTermH _ = Set.empty

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
    pretty = printType . typeFlatForm
instance Pretty TERM where
    pretty = printTerm
instance Pretty FORMULA where
    pretty = printFormula . formulaFlatForm
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl_item (ns,t)) = printNames ns <+> text "::" <+> pretty t
printBasicItem (Axiom_item f) = dot <> pretty f

printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Func ts t) =
  fsep $ prepPunctuate (text "-> ") 
    $ map (printTypeWithPrec funcPrec) (ts ++ [t])
printType (Pi xs x) = text "Pi" <+> printDecls xs <+> printType x

printTypeWithPrec :: Int -> TYPE -> Doc
printTypeWithPrec prec t = if typePrec t >= prec
                              then parens $ printType t
                              else printType t

printTerm :: TERM -> Doc
printTerm t = if (as == [])
                 then pretty x
                 else pretty x <> parens (ppWithCommas as)
              where (x,as) = termFlatForm t

printFormula :: FORMULA -> Doc
printFormula (T) = text "true"
printFormula (F) = text "false"
printFormula (Pred x) = pretty x
printFormula (Equality x y) = pretty x <+> text "==" <+> pretty y
printFormula (Negation f) = notDoc <+> printFormulaWithPrec negPrec f
printFormula (Conjunction xs) = fsep $ prepPunctuate (andDoc <> space)
  $ map (printFormulaWithPrec conjPrec) xs
printFormula (Disjunction xs) = fsep $ prepPunctuate (orDoc <> space)
  $ map (printFormulaWithPrec disjPrec) xs
printFormula (Implication x y) = 
  printFormulaWithPrec (implPrec-1) x 
  <+> implies
  <+> printFormulaWithPrec (implPrec-1) y
printFormula (Equivalence x y) = 
  printFormulaWithPrec (equivPrec-1) x
  <+> equiv
  <+> printFormulaWithPrec (equivPrec-1) y
printFormula (Forall xs f) = forallDoc <+> printDecls xs <+> printFormula f
printFormula (Exists xs f) = exists <+> printDecls xs <+> printFormula f

printFormulaWithPrec :: Int -> FORMULA -> Doc
printFormulaWithPrec prec f = if (formulaPrec f) > prec
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
printDecl (ns, t) = printNames ns <+> colon <+> pretty t

printDecls :: [DECL] -> Doc
printDecls xs = fsep (punctuate semi $ map printDecl xs) <> dot

-- operations on a list of declarations
getVarsFromDecls :: [DECL] -> [NAME]
getVarsFromDecls ds = concatMap fst ds

getVarTypeFromDecls :: NAME -> [DECL] -> Maybe TYPE
getVarTypeFromDecls n ds = case result of
                                Just (_,t) -> Just t
                                Nothing -> Nothing
                           where result = find (\ (ns,_) -> elem n ns) ds

compactDecls :: [DECL] -> [DECL]
compactDecls [] = []
compactDecls [d] = [d]
compactDecls (d1:(d2:ds)) =
  let (ns1,t1) = d1
      (ns2,t2) = d2
      in if (t1 == t2)
            then compactDecls $ (ns1 ++ ns2,t1):ds
            else d1:(compactDecls (d2:ds))

expandDecls :: [DECL] -> [DECL]
expandDecls [] = []
expandDecls (([],_):ds) = expandDecls ds
expandDecls (((n:ns),t):ds) = ([n],t):(expandDecls ((ns,t):ds))

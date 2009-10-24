{- |
Module      :  $Header$
Description :  Abstract syntax for first-order logic with dependent types (DFOL)
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
      typeProperForm,
      piRecForm,
      piFlatForm,
      formulaProperForm,
      quantRecForm,
      quantFlatForm,
      printNames,
      printDecls,
      getVarsFromDecls,
      getVarTypeFromDecls,
      compactDecls,
      expandDecls,
      Translatable,
      translate,
      getNewName  
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
termRecForm (Appl f [a]) = Appl (termRecForm f) [a]
termRecForm (Appl f as) = Appl (termRecForm $ Appl f $ init as) $ [last as]

{- determines the flattened form of a term, i.e. the function symbol
   applied and the argument list -}
termFlatForm :: TERM -> (NAME, [TERM])
termFlatForm (Identifier x) = (x,[])
termFlatForm (Appl f as) = (x, bs ++ as)
                          where (x,bs) = termFlatForm f

{- converts a type into a form where each Pi operator binds exactly
   one argument -}
piRecForm :: TYPE -> TYPE
piRecForm (Pi [] type1) = piRecForm type1
piRecForm (Pi (([n],t):ds) type1) = Pi [([n],t)] $ piRecForm $ Pi ds type1
piRecForm (Pi (((n:ns),t):ds) type1) =
  Pi [([n],t)] $ piRecForm $ Pi ((ns,t):ds) type1
piRecForm t = t

{- converts a type into a flattened form where the Pi operator binds multiple
   arguments and the return type itself does not start with Pi -}
piFlatForm :: TYPE -> TYPE
piFlatForm (Pi ds1 type1) =
  case type1 of
       Pi ds2 type2 -> piFlatForm $ Pi (ds1 ++ ds2) type2
       _ -> Pi (compactDecls ds1) type1
piFlatForm t = t

-- removes empty argument lists
typeProperForm :: TYPE -> TYPE
typeProperForm (Pi [] t) = typeProperForm t
typeProperForm (Func [] t) = typeProperForm t
typeProperForm t = t

{- converts a formula into a form where each quantifier binds exactly
   one variable -}
quantRecForm :: FORMULA -> FORMULA
quantRecForm (Forall [] f) = quantRecForm f
quantRecForm (Exists [] f) = quantRecForm f
quantRecForm (Forall (([n],t):ds) f) =
  Forall [([n],t)] $ quantRecForm $ Forall ds f
quantRecForm (Exists (([n],t):ds) f) =
  Exists [([n],t)] $ quantRecForm $ Exists ds f
quantRecForm (Forall (((n:ns),t):ds) f) =
  Forall [([n],t)] $ quantRecForm $ Forall ((ns,t):ds) f
quantRecForm (Exists (((n:ns),t):ds) f) =
  Exists [([n],t)] $ quantRecForm $ Exists ((ns,t):ds) f
quantRecForm t = t

{- converts a formula into a flattened form where quantifies bind multiple
   arguments and the return type itself does not start with the same
   quantifier -}
quantFlatForm :: FORMULA -> FORMULA
quantFlatForm (Forall ds1 f1) =
  case f1 of
       Forall ds2 f2 -> quantFlatForm $ Forall (ds1 ++ ds2) f2
       _ -> Forall (compactDecls ds1) f1
quantFlatForm (Exists ds1 f1) =
  case f1 of
       Exists ds2 f2 -> quantFlatForm $ Exists (ds1 ++ ds2) f2
       _ -> Exists (compactDecls ds1) f1
quantFlatForm t = t

-- removes empty variable lists
formulaProperForm :: FORMULA -> FORMULA
formulaProperForm (Forall [] f) = formulaProperForm f
formulaProperForm (Exists [] f) = formulaProperForm f
formulaProperForm (Conjunction []) = T
formulaProperForm (Disjunction []) = F
formulaProperForm t = t

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
   translate m s = (translateType m s) . piRecForm . typeProperForm
instance Translatable FORMULA where
   translate m s = (translateFormula m s) . quantRecForm . formulaProperForm

-- expects type in proper and pi-recursive form
translateType :: Map.Map NAME TERM -> Set.Set NAME -> TYPE -> TYPE
translateType _ _ Sort = Sort
translateType _ _ Form = Form
translateType m s (Univ t) = Univ $ translate m s t
translateType m s (Func ts t) =
  Func (map (translate m s) ts) (translate m s t)
translateType m s (Pi [([x],t)] a) =
  let t1 = translate m s t
      x1 = getNewName x s
      a1 = translate (Map.insert x (Identifier x1) m) (Set.insert x1 s) a
      in Pi [([x1],t1)] a1
translateType _ _ t = t

-- expects term in recursive form
translateTerm :: Map.Map NAME TERM -> TERM -> TERM
translateTerm m (Identifier x) = Map.findWithDefault (Identifier x) x m
translateTerm m (Appl f [a]) = Appl (translateTerm m f) [(translateTerm m a)]
translateTerm _ t = t

-- expects formula in proper and quant-recursive form
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
getNewName var names =
  if (Set.notMember var names)
     then var
     else let newVar = Token ((tokStr var) ++ "1") nullRange
              in getNewName newVar names

-- equality
instance Eq TERM where
    u == v = eqTerm (termRecForm u) (termRecForm v)
instance Eq TYPE where
    u == v = eqType (piRecForm $ typeProperForm u)
                    (piRecForm $ typeProperForm v)

-- expects term in recursive form
eqTerm :: TERM -> TERM -> Bool
eqTerm (Identifier x1) (Identifier x2) = x1 == x2
eqTerm (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2]
eqTerm _ _ = False

-- expects type in proper and pi-recursive form
eqType :: TYPE -> TYPE -> Bool
eqType Sort Sort = True
eqType Form Form = True
eqType (Univ t1) (Univ t2) = t1 == t2
eqType (Func (t1:ts1) s1) (Func (t2:ts2) s2) =
  and [t1 == t2, (Func ts1 s1) == (Func ts2 s2)]
eqType (Pi [([n1],t1)] s1) (Pi [([n2],t2)] s2) =
  if (n1 == n2)
     then and [t1 == t2, s1 == s2]
     else let syms1 = getFreeVars $ piRecForm $ typeProperForm s1
              syms2 = getFreeVars $ piRecForm $ typeProperForm s2
              v = getNewName n1 $ Set.union (Set.delete n1 syms1)
                                            (Set.delete n2 syms2)
              type1 = translate (Map.singleton n1 (Identifier v)) syms1 s1
              type2 = translate (Map.singleton n2 (Identifier v)) syms2 s2
              in and [t1 == t2, type1 == type2]
eqType _ _ = False

-- returns a set of unbound identifiers used within a type
-- expects type in proper and pi-recursive form
getFreeVars :: TYPE -> Set.Set NAME
getFreeVars Sort = Set.empty
getFreeVars Form = Set.empty
getFreeVars (Univ t) = getFreeVarsInTerm t
getFreeVars (Func ts t) =
  Set.unions $ [getFreeVars t] ++ (map getFreeVars ts)
getFreeVars (Pi [([n],t)] a) =
  Set.delete n $ Set.union (getFreeVars t) (getFreeVars a)
getFreeVars _ = Set.empty

getFreeVarsInTerm :: TERM -> Set.Set NAME
getFreeVarsInTerm (Identifier x) = Set.singleton x
getFreeVarsInTerm (Appl f as) =
  Set.unions $ [getFreeVarsInTerm f] ++ (map getFreeVarsInTerm as)

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
    pretty = printType . piFlatForm . typeProperForm
instance Pretty TERM where
    pretty = printTerm
instance Pretty FORMULA where
    pretty = printFormula . quantFlatForm . formulaProperForm
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

-- expects type in proper and pi-flat form
printType :: TYPE -> Doc
printType (Sort) = text "Sort"
printType (Form) = text "Form"
printType (Univ t) = pretty t
printType (Func ts t) =
  fsep $ prepPunctuate (text "-> ") $ map (printSubType funcPrec) (ts ++ [t])
printType (Pi xs x) = text "Pi" <+> printDecls xs <+> printType x

printSubType :: Int -> TYPE -> Doc
printSubType prec t = if typePrec t >= prec
                         then parens $ printType t
                         else printType t

printTerm :: TERM -> Doc
printTerm t = if (as == [])
                 then pretty x
                 else pretty x <> parens (ppWithCommas as)
              where (x,as) = termFlatForm t

-- expects formula in proper and quant-flat form
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

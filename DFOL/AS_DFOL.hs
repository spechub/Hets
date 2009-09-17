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
      printNames,
      printDecls,
      getVarsFromDecls,
      getVarTypeFromDecls,
      getVarsDeclaredInType,
      getNewName,
      getRenameMap,
      substitute,
      substitute1
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

-- equality
instance Eq TERM where
    u == v = eqTerm (termRecForm u) (termRecForm v)
instance Eq TYPE where
    u == v = eqType (piRecForm $ typeProperForm u) (piRecForm $ typeProperForm v)

eqTerm :: TERM -> TERM -> Bool
eqTerm (Identifier x1) (Identifier x2) = x1 == x2
eqTerm (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2] 
eqTerm _ _ = False

eqType :: TYPE -> TYPE -> Bool
eqType Sort Sort = True
eqType Form Form = True
eqType (Univ t1) (Univ t2) = t1 == t2
eqType (Func (t1:ts1) s1) (Func (t2:ts2) s2) =
  and [t1 == t2, (Func ts1 s1) == (Func ts2 s2)] 
eqType (Pi [([n1],t1)] s1) (Pi [([n2],t2)] s2) = 
  if (n1 == n2)
     then and [t1 == t2, s1 == s2]
     else let syms1 = Set.delete n1 $ getNamesUsedInType s1
              syms2 = Set.delete n2 $ getNamesUsedInType s2
              v = getNewName n1 $ Set.union syms1 syms2
              type1 = substitute1 n1 (Identifier v) s1
              type2 = substitute1 n2 (Identifier v) s2
              in and [t1 == t2, type1 == type2]
eqType _ _ = False  

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
piRecForm (Pi (((n:ns),t):ds) type1) = Pi [([n],t)] $ piRecForm $ Pi ((ns,t):ds) type1
piRecForm t = t

{- converts a type into a flattened form where the Pi operator binds multiple
   arguments and the return type itself does not contain Pi -}  
piFlatForm :: TYPE -> TYPE
piFlatForm (Pi ds1 type1) = 
  case type1 of
       Pi ds2 type2 -> piFlatForm $ Pi (ds1 ++ ds2) type2
       _ -> Pi (compactDecls ds1) type1
piFlatForm t = t

compactDecls :: [DECL] -> [DECL]
compactDecls [] = []
compactDecls [d] = [d]
compactDecls (d1:(d2:ds)) = 
  let (ns1,t1) = d1
      (ns2,t2) = d2
      in if (t1 == t2) 
            then compactDecls $ (ns1 ++ ns2,t1):ds
            else d1:(compactDecls (d2:ds))

-- removes empty argument lists
typeProperForm :: TYPE -> TYPE
typeProperForm (Pi [] t) = typeProperForm t
typeProperForm (Func [] t) = typeProperForm t
typeProperForm t = t

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
printType (Func ts t) = 
  fsep $ prepPunctuate (text "-> ") $ map (printSubType funcPrec) (ts ++ [t])
printType t = text "Pi" <+> printDecls xs <+> printType x
              where Pi xs x = piFlatForm t 

printSubType :: Int -> TYPE -> Doc
printSubType prec t = if typePrec t >= prec
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

-- returns a list of declared variables from within a type
getVarsDeclaredInType :: TYPE -> [NAME]
getVarsDeclaredInType (Pi ds t) =
  (getVarsFromDecls ds) ++ (getVarsDeclaredInType t)
getVarsDeclaredInType _ = []

-- returns a set of identifiers used within a type
getNamesUsedInType :: TYPE -> Set.Set NAME
getNamesUsedInType Sort = Set.empty
getNamesUsedInType Form = Set.empty
getNamesUsedInType (Univ t) = getNamesUsedInTerm t
getNamesUsedInType (Func ts t) = 
  Set.unions $ [getNamesUsedInType t] ++ (map getNamesUsedInType ts)
getNamesUsedInType (Pi [] t) = getNamesUsedInType t
getNamesUsedInType s = 
  let (Pi [([n],t)] a) = piRecForm s
      in Set.unions [Set.singleton n, getNamesUsedInType t, getNamesUsedInType a]  

getNamesUsedInTerm :: TERM -> Set.Set NAME
getNamesUsedInTerm (Identifier x) = Set.singleton x
getNamesUsedInTerm (Appl f as) = 
  Set.unions $ [getNamesUsedInTerm f] ++ (map getNamesUsedInTerm as)
                            
-- modifies the given name until it is different from each of the names in the input set
getNewName :: NAME -> Set.Set NAME -> NAME
getNewName var names = 
  let newVar = Token ((tokStr var) ++ "1") nullRange
      in if (Set.notMember newVar names)
            then newVar
            else getNewName newVar names

{- modifies the given variable names so that they are different from each of the 
   symbol names in the set as well as from one another; returns a map of the
   renamings -}
getRenameMap :: [NAME] -> Set.Set NAME -> Map.Map NAME NAME
getRenameMap vars1 syms = 
  let vars2 = foldl (\ vs v1 -> let v2 = getNewName v1 (Set.union syms $ Set.fromList vs)
                                    in (vs ++ [v2]))
                    [] 
                    vars1
      in foldl (\ m1 i -> Map.insert (vars1 !! i) (vars2 !! i) m1)
               Map.empty
               [0 .. (length vars1)-1]

{- substitutions in a type: the first map specifies variable renamings
   and the second term/variable substitutions -} 
substitute :: Map.Map NAME NAME -> Map.Map NAME TERM -> TYPE -> TYPE
substitute _ _ Sort = Sort
substitute _ _ Form = Form
substitute map1 map2 (Univ t) = Univ $ substituteInTerm map1 map2 t
substitute map1 map2 (Func ts t) = 
  Func (map (substitute map1 map2) ts) (substitute map1 map2 t)
substitute map1 map2 (Pi ds t) =
  Pi (map (substituteInDecl map1 map2) ds) (substitute map1 map2 t)

substituteInTerm :: Map.Map NAME NAME -> Map.Map NAME TERM -> TERM -> TERM
substituteInTerm map1 map2 t@(Identifier x) = 
  if (Map.member x map1)
     then Identifier $ Map.findWithDefault x x map1
     else if (Map.member x map2)
             then Map.findWithDefault t x map2
             else t    
substituteInTerm map1 map2 (Appl f as) =
  Appl (substituteInTerm map1 map2 f) $ map (substituteInTerm map1 map2) as

substituteInDecl :: Map.Map NAME NAME -> Map.Map NAME TERM -> DECL -> DECL
substituteInDecl map1 map2 (ns,t) = (substituteInNames map1 ns, substitute map1 map2 t)

substituteInNames :: Map.Map NAME NAME -> [NAME] -> [NAME]
substituteInNames map1 ns = 
  map (\n -> if (Map.member n map1) 
                then Map.findWithDefault n n map1 
                else n) 
      ns

-- special case of substitution
substitute1 :: NAME -> TERM -> TYPE -> TYPE
substitute1 n val t = substitute Map.empty (Map.singleton n val) t

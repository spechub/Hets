{- |
Module      :  $Header$
Description :  Abstract syntax for propositional logic extended with QBFs
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de> 
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic extended with QBFs
-}

{-
  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
  <http://www.voronkov.com/lics.cgi>
  
-}

module QBF.AS_BASIC_QBF
    ( FORMULA (..)             -- datatype for Propositional Formulas
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    , SYMB_OR_MAP (..)         -- Symbol or symbol map
    , PRED_ITEM (..)           -- Predicates
    , isPrimForm
    , ID (..)
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

import qualified Data.List as List
import Data.Maybe(isJust) 

-- DrIFT command
{-! global: GetRange !-}

-- | predicates = propositions
data PRED_ITEM = Pred_item [Id.Token] Id.Range
               deriving Show

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEMS)]
                  deriving Show

data BASIC_ITEMS =
    Pred_decl PRED_ITEM
    | Axiom_items [AS_Anno.Annoted (FORMULA)]
    -- pos: dots
    deriving Show

-- | Datatype for QBF formulas
data FORMULA =
    False_atom Id.Range
    -- pos: "False
  | True_atom Id.Range
    -- pos: "True"
  | Predication Id.Token
    -- pos: Propositional Identifiers
  | Negation FORMULA Id.Range
    -- pos: not
  | Conjunction [FORMULA] Id.Range
    -- pos: "/\"s
  | Disjunction [FORMULA] Id.Range
    -- pos: "\/"s
  | Implication FORMULA FORMULA Id.Range
    -- pos: "=>"
  | Equivalence FORMULA FORMULA Id.Range
    -- pos: "<=>"
  | Quantified_ForAll [Id.Token] FORMULA Id.Range
  | Quantified_Exists [Id.Token] FORMULA Id.Range 
    deriving (Show, Ord)

data ID = ID Id.Token (Maybe Id.Token)

instance Eq ID where
	ID t1 (Just t2) == ID t3 (Just t4) = ((t1 == t3) && (t2==t4)) || ((t2==t3) && (t1==t4))
	ID t1 Nothing == ID t2 t3 = (t1 == t2) || ((Just t1) == t3)

--two QBFs are equivalent if bound variables can be renamed such that the QBFs are equal
qbf_make_equal :: (Maybe [ID]) -> FORMULA -> [Id.Token] -> FORMULA -> [Id.Token] -> (Maybe [ID])
qbf_make_equal (Just ids) f ts f1 ts1 = if (length ts) /= (length ts1) then Nothing else case (f,f1) of
  (Predication t,Predication t1) -> if (t == t1) then (Just ids) else
    if (elem t ts) && (elem t1 ts1) then
      if elem (ID t (Just t1)) ids then
        (Just ids)
      else
        if (not (elem (ID t Nothing) ids)) && (not (elem (ID t1 Nothing) ids)) then
          (Just ((ID t (Just t1)):ids))
        else
          Nothing
    else Nothing
  (Negation f_ r1,Negation f1_ r2) -> qbf_make_equal (Just ids) f_ ts f1_ ts1
  (Conjunction (f_:fs) r1,Conjunction (f1_:fs1) r2) -> if (length fs) /= (length fs1) then Nothing else 
    case r of
      Nothing 	-> Nothing
      _		-> qbf_make_equal r (Conjunction fs nullRange) ts (Conjunction fs1 nullRange) ts1
    where
      r = qbf_make_equal (Just ids) f_ ts f1_ ts1
  (Disjunction fs r,Disjunction fs1 r1) -> qbf_make_equal (Just ids) (Conjunction fs r) ts (Conjunction fs1 r1) ts1
  (Implication f_ f1_ r1,Implication f2 f3 r2) -> case r of
    Nothing -> Nothing
    _ -> qbf_make_equal r f1_ ts f3 ts1
   where
     r = qbf_make_equal (Just ids) f_ ts f2 ts1
  (Equivalence f_ f1_ r1,Equivalence f2 f3 r2) -> qbf_make_equal (Just ids) (Implication f_ f1_ r1) ts (Implication f2 f3 r1) ts1
  (Quantified_ForAll ts_ f_ r1,Quantified_ForAll ts1_ f1_ r2) -> case r of
    Nothing -> Nothing
    (Just ids_) -> Just (ids ++  (filter (\(ID x (Just y)) -> ((elem x ts_) && (not (elem y ts1_))) || ((elem x ts1_) && (not (elem y ts_)))) d))
     where
       d = (List.\\) ids_ ids
   where
     r = qbf_make_equal (Just ids) f_ (ts++ts_) f1_ (ts1++ts1_)
  (Quantified_Exists ts_ f_ r,Quantified_Exists ts1_ f1_ r1) -> qbf_make_equal (Just ids) (Quantified_Exists ts_ f_ r) ts (Quantified_Exists ts1_ f1_ r1) ts1
  (_1,_2) -> Nothing

qbf_make_equal Nothing _ _ _ _ = Nothing

--ranges are always equal (see Common/Id.hs) - thus they can be ignored
instance Eq FORMULA where
  False_atom _ == False_atom _ = True
  True_atom _ == True_atom _ = True
  Predication t == Predication t1 = t == t1
  Negation f _ == Negation f1 _ = f == f1
  Conjunction xs _ == Conjunction xs1 _ = xs == xs1
  Disjunction xs _ == Disjunction xs1 _ = xs == xs1
  Implication f f1 _ == Implication f2 f3 _ = (f==f2) && (f1==f3)
  Equivalence f f1 _ == Equivalence f2 f3 _ = (f==f2) && (f1==f3)
  Quantified_ForAll ts f _ == Quantified_ForAll ts1 f1 _ = isJust (qbf_make_equal (Just []) f ts f1 ts1)
  Quantified_Exists ts f _ == Quantified_Exists ts1 f1 _ = isJust (qbf_make_equal (Just []) f ts f1 ts1)
  _ == _ = False
	
data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

newtype SYMB = Symb_id Id.Token
            -- pos: colon
            deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq)

-- All about pretty printing
-- we chose the easy way here :)
instance Pretty FORMULA where
    pretty = printFormula
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
instance Pretty PRED_ITEM where
    pretty = printPredItem

isPrimForm :: FORMULA -> Bool
isPrimForm f = case f of
        True_atom _ -> True
        False_atom _ -> True
        Predication _ -> True
        Negation _ _ -> True
        _ -> False

-- Pretty printing for formulas
printFormula :: FORMULA -> Doc
printFormula frm =
  let ppf p f = (if p f then id else parens) $ printFormula f
      isJunctForm f = case f of
        Implication 		_ _ _	-> False
        Equivalence 		_ _ _	-> False
	Quantified_ForAll 	_ _	_	-> False
	Quantified_Exists 	_ _ _	-> False
        _ -> True
  in case frm of
  False_atom _ -> text falseS
  True_atom _ -> text trueS
  Predication x -> pretty x
  Negation f _ -> notDoc <+> ppf isPrimForm f
  Conjunction xs _ -> sepByArbitrary andDoc $ map (ppf isPrimForm) xs
  Disjunction xs _ -> sepByArbitrary orDoc $ map (ppf isPrimForm) xs
  Implication x y _ -> ppf isJunctForm x <+> implies <+> ppf isJunctForm y
  Equivalence x y _ -> ppf isJunctForm x <+> equiv <+> ppf isJunctForm y
  Quantified_ForAll xs y _ -> forallDoc <+> sepByArbitrary comma (map pretty xs) <+> space <+> ppf isJunctForm y
  Quantified_Exists xs y _ -> exists <+> sepByArbitrary comma (map pretty xs) <+> space <+> ppf isJunctForm y

sepByArbitrary :: Doc -> [Doc] -> Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

printPredItem :: PRED_ITEM -> Doc
printPredItem (Pred_item xs _) = fsep $ map pretty xs

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map pretty xs
printBasicItems (Pred_decl x) = pretty x

printSymbol :: SYMB -> Doc
printSymbol (Symb_id sym) = pretty sym

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = fsep $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (Symb_map source dest  _) =
  pretty source <+> mapsto <+> pretty dest

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = fsep $ map pretty xs

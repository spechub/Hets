{- |
Module      :  $Header$
Description :  Abstract syntax for propositional logic extended with QBFs
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic extended with QBFs

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
  <http://www.voronkov.com/lics.cgi>
-}

module QBF.AS_BASIC_QBF
    ( FORMULA (..)             -- datatype for Propositional Formulas
    , BASICITEMS (..)          -- Items of a Basic Spec
    , BASICSPEC (..)           -- Basic Spec
    , SYMBITEMS (..)           -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMBMAPITEMS (..)        -- Symbol map
    , SYMBORMAP (..)           -- Symbol or symbol map
    , PREDITEM (..)            -- Predicates
    , isPrimForm
    , ID (..)
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

import qualified Data.List as List
import Data.Maybe (isJust)

-- DrIFT command
{-! global: GetRange !-}

-- | predicates = propositions
data PREDITEM = PredItem [Id.Token] Id.Range
               deriving Show

newtype BASICSPEC = BasicSpec [AS_Anno.Annoted BASICITEMS]
                  deriving Show

data BASICITEMS =
    PredDecl PREDITEM
    | AxiomItems [AS_Anno.Annoted FORMULA]
    -- pos: dots
    deriving Show

-- | Datatype for QBF formulas
data FORMULA =
    FalseAtom Id.Range
    -- pos: "False
  | TrueAtom Id.Range
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
  | ForAll [Id.Token] FORMULA Id.Range
  | Exists [Id.Token] FORMULA Id.Range
    deriving (Show, Ord)

data ID = ID Id.Token (Maybe Id.Token)

instance Eq ID where
    ID t1 (Just t2) == ID t3 (Just t4) =
                             ((t1 == t3) && (t2 == t4))
                          || ((t2 == t3) && (t1 == t4))
    ID t1 Nothing == ID t2 t3 = (t1 == t2) || (Just t1 == t3)
    ID _ (Just _) == ID _ Nothing = False

{- two QBFs are equivalent if bound variables
can be renamed such that the QBFs are equal -}
qbfMakeEqual :: Maybe [ID] -> FORMULA -> [Id.Token]
             -> FORMULA -> [Id.Token] -> Maybe [ID]
qbfMakeEqual (Just ids) f ts f1 ts1 = if length ts /= length ts1 then
                                          Nothing
                                      else case (f, f1) of
  (Predication t, Predication t1)
    | t == t1 -> Just ids
    | t `elem` ts && t1 `elem` ts1 -> let tt1 = ID t (Just t1) in
      if tt1 `elem` ids then
        Just ids
      else
        if ID t Nothing `notElem` ids && ID t1 Nothing `notElem` ids then
          Just (tt1 : ids)
        else
          Nothing
    | otherwise -> Nothing
  (Negation f_ _, Negation f1_ _) -> qbfMakeEqual (Just ids) f_ ts f1_ ts1
  (Conjunction (f_ : fs) _, Conjunction (f1_ : fs1) _) ->
    if length fs /= length fs1 then Nothing else
        case r of
            Nothing -> Nothing
            _ -> qbfMakeEqual r
                   (Conjunction fs nullRange) ts
                   (Conjunction fs1 nullRange) ts1
    where
      r = qbfMakeEqual (Just ids) f_ ts f1_ ts1
  (Disjunction fs r, Disjunction fs1 r1) -> qbfMakeEqual (Just ids)
    (Conjunction fs r) ts (Conjunction fs1 r1) ts1
  (Implication f_ f1_ _, Implication f2 f3 _) -> case r of
    Nothing -> Nothing
    _ -> qbfMakeEqual r f1_ ts f3 ts1
   where
     r = qbfMakeEqual (Just ids) f_ ts f2 ts1
  (Equivalence f_ f1_ r1, Equivalence f2 f3 _) -> qbfMakeEqual (Just ids)
    (Implication f_ f1_ r1) ts
    (Implication f2 f3 r1) ts1
  (ForAll ts_ f_ _, ForAll ts1_ f1_ _) -> case r of
    Nothing -> Nothing
    (Just ids_) -> Just (ids ++ filter (\ (ID x my) ->
      let Just y = my in
      (x `elem` ts_ && y `notElem` ts1_) ||
      (x `elem` ts1_ && y `notElem` ts_)) d)
     where
       d = ids_ List.\\ ids
   where
     r = qbfMakeEqual (Just ids) f_ (ts ++ ts_) f1_ (ts1 ++ ts1_)
  (Exists ts_ f_ r, Exists ts1_ f1_ r1) -> qbfMakeEqual (Just ids)
    (Exists ts_ f_ r) ts
    (Exists ts1_ f1_ r1) ts1
  (_1, _2) -> Nothing

qbfMakeEqual Nothing _ _ _ _ = Nothing

-- ranges are always equal (see Common/Id.hs) - thus they can be ignored
instance Eq FORMULA where
  FalseAtom _ == FalseAtom _ = True
  TrueAtom _ == TrueAtom _ = True
  Predication t == Predication t1 = t == t1
  Negation f _ == Negation f1 _ = f == f1
  Conjunction xs _ == Conjunction xs1 _ = xs == xs1
  Disjunction xs _ == Disjunction xs1 _ = xs == xs1
  Implication f f1 _ == Implication f2 f3 _ = (f == f2) && (f1 == f3)
  Equivalence f f1 _ == Equivalence f2 f3 _ = (f == f2) && (f1 == f3)
  ForAll ts f _ == ForAll ts1 f1 _ = isJust (qbfMakeEqual (Just []) f ts f1 ts1)
  Exists ts f _ == Exists ts1 f1 _ = isJust (qbfMakeEqual (Just []) f ts f1 ts1)
  _ == _ = False

data SYMBITEMS = SymbItems [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

newtype SYMB = SymbId Id.Token
            -- pos: colon
            deriving (Show, Eq)

data SYMBMAPITEMS = SymbMapItems [SYMBORMAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

data SYMBORMAP = Symb SYMB
                 | SymbMap SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq)

-- All about pretty printing we chose the easy way here :)
instance Pretty FORMULA where
    pretty = printFormula
instance Pretty BASICSPEC where
    pretty = printBasicSpec
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMBITEMS where
    pretty = printSymbItems
instance Pretty SYMBMAPITEMS where
    pretty = printSymbMapItems
instance Pretty BASICITEMS where
    pretty = printBasicItems
instance Pretty SYMBORMAP where
    pretty = printSymbOrMap
instance Pretty PREDITEM where
    pretty = printPredItem

isPrimForm :: FORMULA -> Bool
isPrimForm f = case f of
        TrueAtom _ -> True
        FalseAtom _ -> True
        Predication _ -> True
        Negation _ _ -> True
        _ -> False

-- Pretty printing for formulas
printFormula :: FORMULA -> Doc
printFormula frm =
  let ppf p f = (if p f then id else parens) $ printFormula f
      isJunctForm f = case f of
        Implication _ _ _ -> False
        Equivalence _ _ _ -> False
        ForAll _ _ _ -> False
        Exists _ _ _ -> False
        _ -> True
  in case frm of
  FalseAtom _ -> text falseS
  TrueAtom _ -> text trueS
  Predication x -> pretty x
  Negation f _ -> notDoc <+> ppf isPrimForm f
  Conjunction xs _ -> sepByArbitrary andDoc $ map (ppf isPrimForm) xs
  Disjunction xs _ -> sepByArbitrary orDoc $ map (ppf isPrimForm) xs
  Implication x y _ -> ppf isJunctForm x <+> implies <+> ppf isJunctForm y
  Equivalence x y _ -> ppf isJunctForm x <+> equiv <+> ppf isJunctForm y
  ForAll xs y _ -> forallDoc <+> sepByArbitrary comma (map pretty xs)
                     <+> space
                     <+> ppf isJunctForm y
  Exists xs y _ -> exists <+> sepByArbitrary comma (map pretty xs)
                     <+> space
                     <+> ppf isJunctForm y

sepByArbitrary :: Doc -> [Doc] -> Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

printPredItem :: PREDITEM -> Doc
printPredItem (PredItem xs _) = fsep $ map pretty xs

printBasicSpec :: BASICSPEC -> Doc
printBasicSpec (BasicSpec xs) = vcat $ map pretty xs

printBasicItems :: BASICITEMS -> Doc
printBasicItems (AxiomItems xs) = vcat $ map pretty xs
printBasicItems (PredDecl x) = pretty x

printSymbol :: SYMB -> Doc
printSymbol (SymbId sym) = pretty sym

printSymbItems :: SYMBITEMS -> Doc
printSymbItems (SymbItems xs _) = fsep $ map pretty xs

printSymbOrMap :: SYMBORMAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (SymbMap source dest _) =
  pretty source <+> mapsto <+> pretty dest

printSymbMapItems :: SYMBMAPITEMS -> Doc
printSymbMapItems (SymbMapItems xs _) = fsep $ map pretty xs

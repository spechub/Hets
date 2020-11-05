{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CASL/Sublogic.hs
Description :  sublogic analysis for CASL
Copyright   :  (c) Pascal Schmidt, C. Maeder, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Sublogic analysis for CASL

This module provides the sublogic functions (as required by Logic.hs)
  for CASL. The functions allow to compute the minimal sublogics needed
  by a given element, to check whether an item is part of a given
  sublogic, and to project an element into a given sublogic.
-}

module CASL.Sublogic
    ( -- * types
      CASL_Sublogics
    , CASL_SL (..)
    , CASL_Formulas (..)
    , SubsortingFeatures (..)
    , SortGenerationFeatures (..)
    -- * class
    , Lattice (..)
    -- * predicates on CASL_SL
    , has_sub
    , has_cons
    -- * functions for SemiLatticeWithTop instance
    , mkTop
    , top
    , caslTop
    , cFol
    , fol
    , cPrenex
    , sublogics_max
    , comp_list
    -- * functions for the creation of minimal sublogics
    , bottom
    , mkBot
    , emptyMapConsFeature
    , need_sub
    , need_pred
    , need_horn
    , need_fol
    , updExtFeature
    -- * functions for Logic instance sublogic to string conversion
    , sublogics_name
    , parseSL
    , parseBool
    -- ** list of all sublogics
    , sublogics_all
    , sDims
    -- * computes the sublogic of a given element
    , sl_sig_items
    , sl_basic_spec
    , sl_opkind
    , sl_op_type
    , sl_op_item
    , sl_pred_item
    , sl_sentence
    , sl_term
    , sl_symb_items
    , sl_symb_map_items
    , sl_sign
    , sl_morphism
    , sl_symbol
    -- * projects an element into a given sublogic
    , pr_basic_spec
    , pr_symb_items
    , pr_symb_map_items
    , pr_sign
    , pr_morphism
    , pr_epsilon
    , pr_symbol
    ) where

import Data.Data
import Data.List
import Data.Maybe
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import Common.Lattice

import Control.Monad

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Fold
import GHC.Generics (Generic)
import Data.Hashable

{- ----------------------------------------------------------------------------
datatypes for CASL sublogics
---------------------------------------------------------------------------- -}

data CASL_Formulas = Atomic  -- ^ atomic logic
                   | Horn    -- ^ positive conditional logic
                   | GHorn   -- ^ generalized positive conditional logic
                   | Prenex  -- ^ formulas in prenex normal form
                   | FOL     -- ^ first-order logic
                   | SOL     -- ^ second-order logic
                   deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable CASL_Formulas

data SubsortingFeatures = NoSub
                        | LocFilSub
                        | Sub
                          deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable SubsortingFeatures

data SortGenerationFeatures =
          NoSortGen
        | SortGen { emptyMapping :: Bool
                    -- ^ Mapping of indexed sorts is empty
                  , onlyInjConstrs :: Bool
                    -- ^ only constructors that are subsort injections
                  } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable SortGenerationFeatures

joinSortGenFeature :: (Bool -> Bool -> Bool)
                   -> SortGenerationFeatures -> SortGenerationFeatures
                   -> SortGenerationFeatures
joinSortGenFeature f x y =
    case x of
      NoSortGen -> y
      SortGen em_x ojc_x -> case y of
          NoSortGen -> x
          SortGen em_y ojc_y -> SortGen (f em_x em_y) (f ojc_x ojc_y)

data CASL_SL a = CASL_SL
    { sub_features :: SubsortingFeatures, -- ^ subsorting
      has_part :: Bool,  -- ^ partiality
      cons_features :: SortGenerationFeatures, -- ^ sort generation constraints
      has_eq :: Bool,    -- ^ equality
      has_pred :: Bool,  -- ^ predicates
      which_logic :: CASL_Formulas, -- ^ first order sublogics
      has_empty_sorts :: Bool, -- ^ may sorts be empty
      ext_features :: a  -- ^ features of extension
    } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable a => Hashable (CASL_SL a)

updExtFeature :: (a -> a) -> CASL_SL a -> CASL_SL a
updExtFeature f s = s { ext_features = f $ ext_features s }

type CASL_Sublogics = CASL_SL ()

{- -----------------------
old selector functions
----------------------- -}

has_sub :: CASL_SL a -> Bool
has_sub sl = case sub_features sl of
             NoSub -> False
             _ -> True

has_cons :: CASL_SL a -> Bool
has_cons sl = case cons_features sl of
              NoSortGen -> False
              _ -> True
{- ---------------------------------------------------------------------------
Special sublogics elements
--------------------------------------------------------------------------- -}

-- top element
mkTop :: a -> CASL_SL a
mkTop = CASL_SL Sub True (SortGen False False) True True SOL True

top :: Lattice a => CASL_SL a
top = mkTop ctop

caslTop :: Lattice a => CASL_SL a
caslTop = top
  { has_empty_sorts = False
  , which_logic = FOL
  }

cFol :: Lattice a => CASL_SL a
cFol = caslTop
  { sub_features = NoSub -- no subsorting
  , has_part = False -- no partiality
  }

fol :: Lattice a => CASL_SL a
fol = caslTop
  { sub_features = NoSub -- no subsorting
  , has_part = False -- no partiality
  , cons_features = NoSortGen -- no sort generation constraints 
  }

cPrenex :: Lattice a => CASL_SL a
cPrenex = cFol {which_logic = Prenex}

mkBot :: a -> CASL_SL a
mkBot = CASL_SL NoSub False NoSortGen False False Atomic False

-- bottom element
bottom :: Lattice a => CASL_SL a
bottom = mkBot bot

need_empty_sorts :: Lattice a => CASL_SL a
need_empty_sorts = bottom { has_empty_sorts = True }

{- the following are used to add a needed feature to a given
sublogic via sublogics_max, i.e. (sublogics_max given needs_part)
will force partiality in addition to what features given already
has included -}

-- minimal sublogics with subsorting
need_sub :: Lattice a => CASL_SL a
need_sub = need_horn { sub_features = Sub }

need_sul :: Lattice a => CASL_SL a
need_sul = need_horn { sub_features = LocFilSub }

-- minimal sublogic with partiality
need_part :: Lattice a => CASL_SL a
need_part = bottom { has_part = True }

emptyMapConsFeature :: SortGenerationFeatures
emptyMapConsFeature = SortGen
  { emptyMapping = True
  , onlyInjConstrs = False }

-- minimal sublogics with sort generation constraints
need_cons :: Lattice a => CASL_SL a
need_cons = bottom
    { cons_features = SortGen { emptyMapping = False
                              , onlyInjConstrs = False} }

need_e_cons :: Lattice a => CASL_SL a
need_e_cons = bottom
    { cons_features = emptyMapConsFeature }

need_s_cons :: Lattice a => CASL_SL a
need_s_cons = bottom
    { cons_features = SortGen { emptyMapping = False
                              , onlyInjConstrs = True} }

need_se_cons :: Lattice a => CASL_SL a
need_se_cons = bottom
    { cons_features = SortGen { emptyMapping = True
                              , onlyInjConstrs = True} }

-- minimal sublogic with equality
need_eq :: Lattice a => CASL_SL a
need_eq = bottom { has_eq = True }

-- minimal sublogic with predicates
need_pred :: Lattice a => CASL_SL a
need_pred = bottom { has_pred = True }

need_horn :: Lattice a => CASL_SL a
need_horn = bottom { which_logic = Horn }

need_fol :: Lattice a => CASL_SL a
need_fol = bottom { which_logic = FOL }

{- ---------------------------------------------------------------------------
Functions to generate a list of all sublogics for CASL
--------------------------------------------------------------------------- -}

{- all elements
create a list of all CASL sublogics by generating all possible
feature combinations and then filtering illegal ones out -}
sublogics_all :: Lattice a => [a] -> [CASL_SL a]
sublogics_all l = bottom : map mkBot l ++ concat (sDims [])
 ++ let subPAtom = (sublogics_max need_part need_pred) { sub_features = Sub } in
    [ sublogics_max need_fol need_eq
    , comp_list [subPAtom, need_horn, need_eq]
    , subPAtom
    , sublogics_max subPAtom need_cons
    , cFol, caslTop, top]

sDims :: Lattice a => [[a]] -> [[CASL_SL a]]
sDims l = let
  t = True
  b = bottom
  bools = [True, False]
  in
  map (map mkBot) l ++
  [ [ b { sub_features = s_f } | s_f <- [LocFilSub, Sub]]
  , [b { has_part = t } ]
  , [b { cons_features = c_f } | c_f <- [ SortGen m s | m <- bools, s <- bools]]
  , [b { has_eq = t } ]
  , [b { has_pred = t } ]
  , [b { has_empty_sorts = t } ]
  , [b { which_logic = fo } | fo <- reverse [SOL, FOL, Prenex, GHorn, Horn]]]

{- ----------------------------------------------------------------------------
Conversion functions (to String)
---------------------------------------------------------------------------- -}

formulas_name :: Bool -> CASL_Formulas -> String
formulas_name b f = let Just s = lookup (b, f) nameList in s

nameList :: [((Bool, CASL_Formulas), String)]
nameList =
  [ ((True, SOL), "SOL")
  , ((False, SOL), "SOAlg")
  , ((True, FOL), "FOL")
  , ((False, FOL), "FOAlg")
  , ((True, Prenex), "Prenex")
  , ((False,Prenex), "PrenexAlg")
  , ((True, GHorn), "GHorn")
  , ((False, GHorn), "GCond")
  , ((True, Horn), "Horn")
  , ((False, Horn), "Cond")
  , ((True, Atomic), "Atom")
  , ((False, Atomic), "Eq")]

sublogics_name :: (a -> String) -> CASL_SL a -> String
sublogics_name f x = f (ext_features x)
                    ++ (case sub_features x of
                         NoSub -> ""
                         LocFilSub -> "Sul"
                         Sub -> "Sub")
                    ++ (if has_part x then "P" else "")
                    ++ (if has_cons x
                        then (if onlyInjConstrs (cons_features x)
                              then "s" else "") ++
                             (if emptyMapping (cons_features x)
                              then "e" else "") ++ "C"
                         else "")
                    ++ formulas_name (has_pred x) (which_logic x)
                    ++ (if has_eq x then "=" else "")
                    ++ if has_empty_sorts x then "E" else ""

parseBool :: String -> String -> (Bool, String)
parseBool p s = case stripPrefix p s of
        Just r -> (True, r)
        Nothing -> (False, s)

parseSL :: (String -> Maybe (a, String)) -> String -> Maybe (CASL_SL a)
parseSL f s0 = do
  (a, s1) <- f s0
  (sub, s2) <- case stripPrefix "Su" s1 of
    Just r -> case r of
      c : t -> case c of
        'l' -> Just (LocFilSub, t)
        'b' -> Just (Sub, t)
        _ -> Nothing
      "" -> Nothing
    Nothing -> Just (NoSub, s1)
  let (pa, s3) = parseBool "P" s2
      (c, s4) = parseCons s3
  ((pr, l), s5) <- parseForm s4
  let (eq, s6) = parseBool "=" s5
      (es, s7) = parseBool "E" s6
  unless (null s7) Nothing
  return (mkBot a)
    { sub_features = sub
    , has_part = pa
    , cons_features = c
    , has_pred = pr
    , which_logic = l
    , has_eq = eq
    , has_empty_sorts = es }

parseForm :: String -> Maybe ((Bool, CASL_Formulas), String)
parseForm s = foldr (\ (q, p) m -> case m of
  Just _ -> m
  Nothing -> case stripPrefix p s of
    Just r -> Just (q, r)
    Nothing -> m) Nothing nameList

parseCons :: String -> (SortGenerationFeatures, String)
parseCons s = case stripPrefix "seC" s of
  Just r -> (SortGen True True, r)
  Nothing -> case stripPrefix "sC" s of
    Just r -> (SortGen False True, r)
    Nothing -> case stripPrefix "eC" s of
      Just r -> (SortGen True False, r)
      Nothing -> case stripPrefix "C" s of
        Just r | not $ isPrefixOf "ond" r -> (SortGen False False, r)
        _ -> (NoSortGen, s)


{- ----------------------------------------------------------------------------
join or max functions
---------------------------------------------------------------------------- -}

sublogics_join :: (Bool -> Bool -> Bool)
               -> (SubsortingFeatures -> SubsortingFeatures
                   -> SubsortingFeatures)
               -> (SortGenerationFeatures -> SortGenerationFeatures
                   -> SortGenerationFeatures)
               -> (CASL_Formulas -> CASL_Formulas -> CASL_Formulas)
               -> (a -> a -> a)
               -> CASL_SL a -> CASL_SL a -> CASL_SL a
sublogics_join jB jS jC jF jE a b = CASL_SL
    { sub_features = jS (sub_features a) (sub_features b)
    , ext_features = jE (ext_features a) (ext_features b)
    , has_part = jB (has_part a) $ has_part b
    , cons_features = jC (cons_features a) (cons_features b)
    , has_eq = jB (has_eq a) $ has_eq b
    , has_pred = jB (has_pred a) $ has_pred b
    , has_empty_sorts = jB (has_empty_sorts a) $ has_empty_sorts b
    , which_logic = jF (which_logic a) (which_logic b)
    }

sublogics_max :: Lattice a => CASL_SL a -> CASL_SL a
              -> CASL_SL a
sublogics_max = sublogics_join max max (joinSortGenFeature min) max cjoin

{- ----------------------------------------------------------------------------
Helper functions
---------------------------------------------------------------------------- -}

-- compute sublogics from a list of sublogics
comp_list :: Lattice a => [CASL_SL a] -> CASL_SL a
comp_list = foldl sublogics_max bottom

{- map a function returning Maybe over a list of arguments
. a list of Pos is maintained by removing an element if the
function f returns Nothing on the corresponding element of
the argument list
. leftover elements in the Pos list after the argument
list is exhausted are appended at the end with Nothing
as a substitute for f's result -}
mapMaybePos :: [Pos] -> (a -> Maybe b) -> [a] -> [(Maybe b, Pos)]
mapMaybePos [] _ _ = []
mapMaybePos (p1 : pl) f [] = (Nothing, p1) : mapMaybePos pl f []
mapMaybePos (p1 : pl) f (h : t) = let res = f h in
  (if isJust res then ((res, p1) :) else id) $ mapMaybePos pl f t

{- map with partial function f on Maybe type
will remove elements from given Pos list for elements of [a]
where f returns Nothing
given number of elements from the beginning of Range are always
kept -}
mapPos :: Int -> Range -> (a -> Maybe b) -> [a] -> ([b], Range)
mapPos c (Range p) f l = let
                   (res, pos) = unzip $ mapMaybePos (drop c p) f l
                 in
                   (catMaybes res, Range (take c p ++ pos))

{- ----------------------------------------------------------------------------
Functions to analyse formulae
---------------------------------------------------------------------------- -}

{- ---------------------------------------------------------------------------
   These functions are based on Till Mossakowski's paper "Sublanguages of
   CASL", which is CoFI Note L-7. The functions implement an adaption of
   the reduced grammar given there for formulae in a specific expression
   logic by, checking whether a formula would match the productions from the
   grammar.
--------------------------------------------------------------------------- -}

sl_form_level :: (f -> CASL_Formulas)
              -> (Bool, Bool) -> FORMULA f -> CASL_Formulas
sl_form_level ff (isCompound, leftImp) phi = let
     subl = sl_form_level_aux ff (isCompound, leftImp) phi
  in if subl == FOL 
      then if testPrenex True ff phi then Prenex
                                  else FOL
      else subl 

sl_form_level_aux :: (f -> CASL_Formulas)
              -> (Bool, Bool) -> FORMULA f -> CASL_Formulas
sl_form_level_aux ff (isCompound, leftImp) phi =
 case phi of
   Quantification q _ f _ ->
       let ql = sl_form_level_aux ff (isCompound, leftImp) f
       in if is_atomic_q q then ql else max FOL ql
   Junction j l _ -> maximum $ case j of
      Con -> FOL : map (sl_form_level_aux ff (True, leftImp)) l
      Dis -> FOL : map (sl_form_level_aux ff (False, False)) l
   Relation l1 c l2 _ -> maximum $ sl_form_level_aux ff (True, True) l1
     : case c of
         Equivalence -> [ sl_form_level_aux ff (True, True) l2
                        , if leftImp then FOL else GHorn ]
         _ -> [ sl_form_level_aux ff (True, False) l2
              , if leftImp then FOL else
                    if isCompound then GHorn else Horn ]
   Negation f _ -> max FOL $ sl_form_level_aux ff (False, False) f
   Atom b _ -> if b then Atomic else FOL
   Equation _ e _ _
     | e == Existl -> Atomic
     | leftImp -> FOL
     | otherwise -> Horn
   QuantOp {} -> SOL  -- it can't get worse
   QuantPred {} -> SOL
   ExtFORMULA f -> ff f
   _ -> Atomic

testPrenex :: Bool -> (f -> CASL_Formulas) -> FORMULA f -> Bool
testPrenex topQ ff phi = 
  case phi of 
    Quantification _ _ phi' _ -> if topQ then testPrenex True ff phi' else False
    Junction _ l _ -> foldl (\b x -> b && testPrenex False ff x) True l
    Relation l1 _ l2 _ -> testPrenex False ff l1 && testPrenex False ff l2
    Negation f _ -> testPrenex False ff f
    Atom _ _ -> True
    Equation _ _ _ _ -> True 
    QuantOp {} -> error "should not get quant ops in FOL"
    QuantPred {} -> error "should not get quant preds in FOL"
    ExtFORMULA f -> if ff f == Prenex then True else False
    _ -> True 
    

-- QUANTIFIER
is_atomic_q :: QUANTIFIER -> Bool
is_atomic_q Universal = True
is_atomic_q _ = False

-- compute logic of a formula by checking all logics in turn
get_logic :: Lattice a => (f -> CASL_SL a)
          -> FORMULA f -> CASL_SL a
get_logic ff f = bottom
  { which_logic = sl_form_level (which_logic . ff) (False, False) f }

-- for the formula inside a subsort-defn
get_logic_sd :: Lattice a => (f -> CASL_SL a)
             -> FORMULA f -> CASL_SL a
get_logic_sd ff f = bottom
  { which_logic =
    max Horn $ sl_form_level (which_logic . ff) (False, False) f }

{- ----------------------------------------------------------------------------
Functions to compute minimal sublogic for a given element, these work
by recursing into all subelements
---------------------------------------------------------------------------- -}

sl_basic_spec :: Lattice a => (b -> CASL_SL a)
              -> (s -> CASL_SL a)
              -> (f -> CASL_SL a)
              -> BASIC_SPEC b s f -> CASL_SL a
sl_basic_spec bf sf ff (Basic_spec l) =
    comp_list $ map (sl_basic_items bf sf ff . item) l
sl_basic_items :: Lattice a => (b -> CASL_SL a)
              -> (s -> CASL_SL a)
              -> (f -> CASL_SL a)
              -> BASIC_ITEMS b s f -> CASL_SL a
sl_basic_items bf sf ff bi = case bi of
    Sig_items i -> sl_sig_items sf ff i
    Free_datatype sk l _ -> needsEmptySorts sk
        $ comp_list $ map (sl_datatype_decl . item) l
    Sort_gen l _ -> sublogics_max need_se_cons
        $ comp_list $ map (sl_sig_items sf ff . item) l
    Var_items l _ -> comp_list $ map sl_var_decl l
    Local_var_axioms d l _ -> comp_list
        $ map sl_var_decl d ++ map (sl_formula ff . item) l
    Axiom_items l _ -> comp_list $ map (sl_formula ff . item) l
    Ext_BASIC_ITEMS b -> bf b

needsEmptySorts :: Lattice a => SortsKind -> CASL_SL a -> CASL_SL a
needsEmptySorts sk = case sk of
    NonEmptySorts -> id
    PossiblyEmptySorts -> sublogics_max need_empty_sorts

sl_sig_items :: Lattice a => (s -> CASL_SL a)
              -> (f -> CASL_SL a)
              -> SIG_ITEMS s f -> CASL_SL a
sl_sig_items sf ff si = case si of
    Sort_items sk l _ -> needsEmptySorts sk
          $ comp_list $ map (sl_sort_item ff . item) l
    Op_items l _ -> comp_list $ map (sl_op_item ff . item) l
    Pred_items l _ -> comp_list $ map (sl_pred_item ff . item) l
    Datatype_items sk l _ -> needsEmptySorts sk
          $ comp_list $ map (sl_datatype_decl . item) l
    Ext_SIG_ITEMS s -> sf s

{- Subsort_defn needs to compute the expression logic needed seperately
because the expressiveness allowed in the formula may be different
from more general formulae in the same expression logic -}
sl_sort_item :: Lattice a => (f -> CASL_SL a)
             -> SORT_ITEM f -> CASL_SL a
sl_sort_item ff si = case si of
    Subsort_decl {} -> need_sul
    Subsort_defn _ _ _ f _ -> sublogics_max
                                        (get_logic_sd ff $ item f)
                                        (sublogics_max need_sul
                                        (sl_formula ff $ item f))
    Iso_decl _ _ -> need_sul
    _ -> bottom

sl_op_item :: Lattice a => (f -> CASL_SL a)
           -> OP_ITEM f -> CASL_SL a
sl_op_item ff oi = case oi of
    Op_decl _ t l _ -> sublogics_max (sl_op_type t)
                               (comp_list $ map (sl_op_attr ff) l)
    Op_defn _ h t _ -> sublogics_max (sl_op_head h)
                                             (sl_term ff $ item t)

sl_op_attr :: Lattice a => (f -> CASL_SL a)
           -> OP_ATTR f -> CASL_SL a
sl_op_attr ff oa = case oa of
    Unit_op_attr t -> sl_term ff t
    _ -> need_eq

sl_op_type :: Lattice a => OP_TYPE -> CASL_SL a
sl_op_type ot = case ot of
    Op_type Partial _ _ _ -> need_part
    _ -> bottom

sl_op_head :: Lattice a => OP_HEAD -> CASL_SL a
sl_op_head oh = case oh of
    Op_head Partial _ _ _ -> need_part
    _ -> bottom

sl_pred_item :: Lattice a => (f -> CASL_SL a)
             -> PRED_ITEM f -> CASL_SL a
sl_pred_item ff i = case i of
    Pred_decl {} -> need_pred
    Pred_defn _ _ f _ -> sublogics_max need_pred (sl_formula ff $ item f)

sl_datatype_decl :: Lattice a => DATATYPE_DECL -> CASL_SL a
sl_datatype_decl (Datatype_decl _ l _) =
    comp_list $ map (sl_alternative . item) l

sl_alternative :: Lattice a => ALTERNATIVE -> CASL_SL a
sl_alternative a = case a of
    Alt_construct Total _ l _ -> comp_list $ map sl_components l
    Alt_construct Partial _ _ _ -> need_part
    Subsorts _ _ -> need_sul

sl_components :: Lattice a => COMPONENTS -> CASL_SL a
sl_components c = case c of
    Cons_select Partial _ _ _ -> need_part
    _ -> bottom

sl_var_decl :: Lattice a => VAR_DECL -> CASL_SL a
sl_var_decl _ = bottom

{- without subsorts casts are trivial and would not even require
   need_part, but testing sortOfTerm is not save for formulas in basic specs
   that are only parsed (and resolved) but not enriched with sorts -}

slRecord :: Lattice a => (f -> CASL_SL a) -> Record f (CASL_SL a) (CASL_SL a)
slRecord ff = (constRecord ff comp_list bottom)
  { foldPredication = \ _ _ l _ -> comp_list $ need_pred : l
  , foldEquation = \ _ t _ u _ -> comp_list [need_eq, t, u]
  , foldSort_gen_ax = \ _ constraints _ ->
      case recover_Sort_gen_ax constraints of
      (_, ops, m) -> case (m, filter (\ o -> case o of
                   Op_name _ -> True
                   Qual_op_name n _ _ ->
                       not (isInjName n)) ops) of
        ([], []) -> need_se_cons
        ([], _) -> need_e_cons
        (_, []) -> need_s_cons
        _ -> need_cons
  , foldQuantPred = \ _ _ _ f -> sublogics_max need_pred f
  , foldCast = \ _ t _ _ -> sublogics_max need_part t
  }

sl_term :: Lattice a => (f -> CASL_SL a) -> TERM f -> CASL_SL a
sl_term = foldTerm . slRecord

sl_formula :: Lattice a => (f -> CASL_SL a)
           -> FORMULA f -> CASL_SL a
sl_formula ff f = sublogics_max (get_logic ff f) (sl_form ff f)

sl_form :: Lattice a => (f -> CASL_SL a)
        -> FORMULA f -> CASL_SL a
sl_form = foldFormula . slRecord

sl_symb_items :: Lattice a => SYMB_ITEMS -> CASL_SL a
sl_symb_items (Symb_items k l _) = sublogics_max (sl_symb_kind k)
                                   (comp_list $ map sl_symb l)

sl_symb_kind :: Lattice a => SYMB_KIND -> CASL_SL a
sl_symb_kind pk = case pk of
    Preds_kind -> need_pred
    _ -> bottom

sl_symb :: Lattice a => SYMB -> CASL_SL a
sl_symb s = case s of
    Symb_id _ -> bottom
    Qual_id _ t _ -> sl_type t

sl_type :: Lattice a => TYPE -> CASL_SL a
sl_type ty = case ty of
    O_type t -> sl_op_type t
    P_type _ -> need_pred
    _ -> bottom

sl_symb_map_items :: Lattice a => SYMB_MAP_ITEMS -> CASL_SL a
sl_symb_map_items (Symb_map_items k l _) = sublogics_max (sl_symb_kind k)
                                          (comp_list $ map sl_symb_or_map l)

sl_symb_or_map :: Lattice a => SYMB_OR_MAP -> CASL_SL a
sl_symb_or_map syms = case syms of
    Symb s -> sl_symb s
    Symb_map s t _ -> sublogics_max (sl_symb s) (sl_symb t)

{- the maps have no influence since all sorts, ops, preds in them
must also appear in the signatures, so any features needed by
them will be included by just checking the signatures -}

sl_sign :: Lattice a => (e -> CASL_SL a) -> Sign f e -> CASL_SL a
sl_sign f s =
    let rel = sortRel s
        subs | Rel.noPairs rel = bottom
             | Rel.locallyFiltered rel = need_sul
             | otherwise = need_sub
        esorts = if Set.null $ emptySortSet s then bottom
                 else need_empty_sorts
        preds = if MapSet.null $ predMap s then bottom else need_pred
        partial = if any isPartial $ Set.toList
                  $ MapSet.elems $ opMap s then need_part else bottom
        in comp_list [subs, esorts, preds, partial, f $ extendedInfo s]

sl_sentence :: Lattice a => (f -> CASL_SL a) -> FORMULA f -> CASL_SL a
sl_sentence = sl_formula

sl_morphism :: Lattice a => (e -> CASL_SL a) -> Morphism f e m -> CASL_SL a
sl_morphism f m = sublogics_max (sl_sign f $ msource m) (sl_sign f $ mtarget m)

sl_symbol :: Lattice a => Symbol -> CASL_SL a
sl_symbol (Symbol _ t) = sl_symbtype t

sl_symbtype :: Lattice a => SymbType -> CASL_SL a
sl_symbtype st = case st of
    OpAsItemType t -> sl_optype t
    PredAsItemType _ -> need_pred
    _ -> bottom

sl_optype :: Lattice a => OpType -> CASL_SL a
sl_optype = sl_opkind . opKind

sl_opkind :: Lattice a => OpKind -> CASL_SL a
sl_opkind fk = case fk of
    Partial -> need_part
    _ -> bottom

{- ----------------------------------------------------------------------------
projection functions
---------------------------------------------------------------------------- -}

sl_in :: Lattice a => CASL_SL a -> CASL_SL a -> Bool
sl_in given new = sublogics_max given new == given

in_x :: Lattice a => CASL_SL a -> b -> (b -> CASL_SL a) -> Bool
in_x l x f = sl_in l (f x)

-- process Annoted type like simple type, simply keep all annos
pr_annoted :: CASL_SL s -> (CASL_SL s -> a -> Maybe a)
              -> Annoted a -> Maybe (Annoted a)
pr_annoted sl f a =
  fmap (`replaceAnnoted` a) $ f sl (item a)

{- project annoted type, by-producing a [SORT]
used for projecting datatypes: sometimes it is necessary to
introduce a SORT_DEFN for a datatype that was erased
completely, for example by only having partial constructors
and partiality forbidden in the desired sublogic - the sort
name may however still be needed for formulas because it can
appear there like in (forall x,y:Datatype . x=x), a formula
that does not use partiality (does not use any constructor
or selector) -}
pr_annoted_dt :: CASL_SL s
              -> (CASL_SL s -> a -> (Maybe a, [SORT]))
              -> Annoted a -> (Maybe (Annoted a), [SORT])
pr_annoted_dt sl f a =
    let (res, lst) = f sl (item a)
    in (fmap (`replaceAnnoted` a) res
       , lst)

-- keep an element if its computed sublogic is in the given sublogic
pr_check :: Lattice a => CASL_SL a -> (b -> CASL_SL a)
         -> b -> Maybe b
pr_check l f e = if in_x l e f then Just e else Nothing

checkRecord :: CASL_SL a -> (CASL_SL a -> f -> Maybe (FORMULA f))
            -> Record f (FORMULA f) (TERM f)
checkRecord l ff = (mapRecord id)
          { foldExtFORMULA = \ o _ -> case o of
              ExtFORMULA f -> fromMaybe (error "checkRecord") $ ff l f
              _ -> error "checkRecord.foldExtFORMULA" }

toCheck :: Lattice a => CASL_SL a
        -> (CASL_SL a -> f -> Maybe (FORMULA f))
        -> f -> CASL_SL a
toCheck l ff = maybe top (const l) . ff l

pr_formula :: Lattice a => (CASL_SL a -> f -> Maybe (FORMULA f))
           -> CASL_SL a -> FORMULA f -> Maybe (FORMULA f)
pr_formula ff l =
    fmap (foldFormula $ checkRecord l ff)
    . pr_check l (sl_formula $ toCheck l ff)

pr_term :: Lattice a => (CASL_SL a -> f -> Maybe (FORMULA f))
        -> CASL_SL a -> TERM f -> Maybe (TERM f)
pr_term ff l =
    fmap (foldTerm $ checkRecord l ff)
    . pr_check l (sl_term $ toCheck l ff)

-- make full Annoted Sig_items out of a SORT list
pr_make_sorts :: [SORT] -> Annoted (BASIC_ITEMS b s f)
pr_make_sorts s =
  Annoted (Sig_items (Sort_items NonEmptySorts
             [Annoted (Sort_decl s nullRange) nullRange [] []]
             nullRange))
          nullRange [] []

{- when processing BASIC_SPEC, add a Sort_decl in front for sorts
defined by DATATYPE_DECLs that had to be removed completely,
otherwise formulas might be broken by the missing sorts, thus
breaking the projection -}
pr_basic_spec :: Lattice a =>
                 (CASL_SL a -> b -> (Maybe (BASIC_ITEMS b s f), [SORT]))
              -> (CASL_SL a -> s -> (Maybe (SIG_ITEMS s f), [SORT]))
              -> (CASL_SL a -> f -> Maybe (FORMULA f))
              -> CASL_SL a -> BASIC_SPEC b s f -> BASIC_SPEC b s f
pr_basic_spec fb fs ff l (Basic_spec s) =
  let
    res = map (pr_annoted_dt l $ pr_basic_items fb fs ff) s
    items = mapMaybe fst res
    toAdd = concatMap snd res
    ret = if null toAdd then
              items
            else
              pr_make_sorts toAdd : items
  in
    Basic_spec ret

{- returns a non-empty list of [SORT] if datatypes had to be removed
completely -}
pr_basic_items :: Lattice a =>
    (CASL_SL a -> b -> (Maybe (BASIC_ITEMS b s f), [SORT]))
    -> (CASL_SL a -> s -> (Maybe (SIG_ITEMS s f), [SORT]))
    -> (CASL_SL a -> f -> Maybe (FORMULA f))
    -> CASL_SL a -> BASIC_ITEMS b s f
    -> (Maybe (BASIC_ITEMS b s f), [SORT])
pr_basic_items fb fs ff l bi = case bi of
    Sig_items s ->
               let
                 (res, lst) = pr_sig_items fs ff l s
               in
                 if isNothing res then
                   (Nothing, lst)
                 else
                   (Just (Sig_items (fromJust res)), lst)
    Free_datatype sk d p ->
               let
                 (res, pos) = mapPos 2 p (pr_annoted l pr_datatype_decl) d
                 lst = pr_lost_dt l (map item d)
               in
                 if null res then
                   (Nothing, lst)
                 else
                   (Just (Free_datatype sk res pos), lst)
    Sort_gen s p ->
               if has_cons l then
                 let
                   tmp = map (pr_annoted_dt l $ pr_sig_items fs ff) s
                   res = mapMaybe fst tmp
                   lst = concatMap snd tmp
                 in
                   if null res then
                     (Nothing, lst)
                   else
                     (Just (Sort_gen res p), lst)
               else
                 (Nothing, [])
    Var_items v p -> (Just (Var_items v p), [])
    Local_var_axioms v f p ->
               let
                 (res, pos) = mapPos (length v) p
                              (pr_annoted l $ pr_formula ff) f
               in
                 if null res then
                   (Nothing, [])
                 else
                   (Just (Local_var_axioms v res pos), [])
    Axiom_items f p ->
               let
                 (res, pos) = mapPos 0 p (pr_annoted l $ pr_formula ff) f
               in
                 if null res then
                   (Nothing, [])
                 else
                   (Just (Axiom_items res pos), [])
    Ext_BASIC_ITEMS b -> fb l b

pr_datatype_decl :: CASL_SL a -> DATATYPE_DECL -> Maybe DATATYPE_DECL
pr_datatype_decl l (Datatype_decl s a p) =
                 let
                   (res, pos) = mapPos 1 p (pr_annoted l pr_alternative) a
                 in
                   if null res then
                     Nothing
                   else
                     Just (Datatype_decl s res pos)

pr_alternative :: CASL_SL a -> ALTERNATIVE -> Maybe ALTERNATIVE
pr_alternative l alt = case alt of
    Alt_construct Total n c p ->
               let
                 (res, pos) = mapPos 1 p (pr_components l) c
               in
                 if null res then
                   Nothing
                 else
                   Just (Alt_construct Total n res pos)
    Alt_construct Partial _ _ _ ->
             if has_part l then
               Just alt
             else
               Nothing
    Subsorts s p ->
               if has_sub l then
                 Just (Subsorts s p)
               else
                 Nothing

pr_components :: CASL_SL a -> COMPONENTS -> Maybe COMPONENTS
pr_components l sel = case sel of
    Cons_select Partial _ _ _ ->
              if has_part l then
                Just sel
              else
                Nothing
    _ -> Just sel

{- takes a list of datatype declarations and checks whether a
whole declaration is invalid in the given sublogic - if this
is the case, the sort that would be declared by the type is
added to a list of SORT that is emitted -}
pr_lost_dt :: CASL_SL a -> [DATATYPE_DECL] -> [SORT]
pr_lost_dt sl = concatMap (\ dt@(Datatype_decl s _ _) ->
                     case pr_datatype_decl sl dt of
                       Nothing -> [s]
                       _ -> [])

pr_symbol :: Lattice a => CASL_SL a -> Symbol -> Maybe Symbol
pr_symbol l = pr_check l sl_symbol

{- returns a non-empty list of [SORT] if datatypes had to be removed
completely -}
pr_sig_items :: Lattice a =>
    (CASL_SL a -> s -> (Maybe (SIG_ITEMS s f), [SORT]))
    -> (CASL_SL a -> f -> Maybe (FORMULA f))
    -> CASL_SL a -> SIG_ITEMS s f -> (Maybe (SIG_ITEMS s f), [SORT])
pr_sig_items sf ff l si = case si of
    Sort_items sk s p ->
             let
               (res, pos) = mapPos 1 p (pr_annoted l pr_sort_item) s
             in
               if null res then
                 (Nothing, [])
               else
                 (Just (Sort_items sk res pos), [])
    Op_items o p ->
             let
               (res, pos) = mapPos 1 p (pr_annoted l $ pr_op_item ff) o
             in
               if null res then
                 (Nothing, [])
               else
                 (Just (Op_items res pos), [])
    Pred_items i p ->
             if has_pred l then
               (Just (Pred_items i p), [])
             else
               (Nothing, [])
    Datatype_items sk d p ->
             let
               (res, pos) = mapPos 1 p (pr_annoted l pr_datatype_decl) d
               lst = pr_lost_dt l (map item d)
             in
               if null res then
                 (Nothing, lst)
               else
                 (Just (Datatype_items sk res pos), lst)
    Ext_SIG_ITEMS s -> sf l s

pr_op_item :: Lattice a => (CASL_SL a -> f -> Maybe (FORMULA f))
           -> CASL_SL a -> OP_ITEM f -> Maybe (OP_ITEM f)
pr_op_item ff l oi = case oi of
      Op_defn o h f r -> do
        g <- pr_annoted l (pr_term ff) f
        return $ Op_defn o h g r
      _ -> Just oi

{- subsort declarations and definitions are reduced to simple
sort declarations if the sublogic disallows subsorting to
avoid loosing sorts in the projection -}
pr_sort_item :: CASL_SL a -> SORT_ITEM f -> Maybe (SORT_ITEM f)
pr_sort_item _ (Sort_decl s p) = Just (Sort_decl s p)
pr_sort_item l (Subsort_decl sl s p) =
             Just $ if has_sub l then Subsort_decl sl s p
                    else Sort_decl (s : sl) nullRange
pr_sort_item l (Subsort_defn s1 v s2 f p) =
             Just $ if has_sub l then Subsort_defn s1 v s2 f p
                    else Sort_decl [s1] nullRange
pr_sort_item _ (Iso_decl s p) = Just (Iso_decl s p)

pr_symb_items :: Lattice a => CASL_SL a -> SYMB_ITEMS
              -> Maybe SYMB_ITEMS
pr_symb_items l (Symb_items k s p) =
              if in_x l k sl_symb_kind then
                let
                  (res, pos) = mapPos 1 p (pr_symb l) s
                in
                  if null res then
                    Nothing
                  else
                    Just (Symb_items k res pos)
              else
                Nothing

pr_symb_map_items :: Lattice a => CASL_SL a -> SYMB_MAP_ITEMS
                  -> Maybe SYMB_MAP_ITEMS
pr_symb_map_items l (Symb_map_items k s p) =
                  if in_x l k sl_symb_kind then
                    let
                      (res, pos) = mapPos 1 p (pr_symb_or_map l) s
                    in
                      if null res then
                        Nothing
                      else
                        Just (Symb_map_items k res pos)
                  else
                    Nothing

pr_symb_or_map :: Lattice a => CASL_SL a -> SYMB_OR_MAP
               -> Maybe SYMB_OR_MAP
pr_symb_or_map l (Symb s) =
               let
                 res = pr_symb l s
               in
                 if isNothing res then
                   Nothing
                 else
                   Just (Symb (fromJust res))
pr_symb_or_map l (Symb_map s t p) =
               let
                 a = pr_symb l s
                 b = pr_symb l t
               in
                 if isJust a && isJust b then
                   Just (Symb_map s t p)
                 else
                   Nothing

pr_symb :: Lattice a => CASL_SL a -> SYMB -> Maybe SYMB
pr_symb _ (Symb_id i) = Just (Symb_id i)
pr_symb l (Qual_id i t p) =
        if in_x l t sl_type then
          Just (Qual_id i t p)
        else
          Nothing

pr_sign :: CASL_SL a -> Sign f e -> Sign f e
pr_sign _sl s = s -- do something here

pr_morphism :: Lattice a => CASL_SL a -> Morphism f e m
            -> Morphism f e m
pr_morphism l m =
     m { msource = pr_sign l $ msource m
       , mtarget = pr_sign l $ mtarget m
       , op_map = pr_op_map l $ op_map m
       , pred_map = pr_pred_map l $ pred_map m }

{- predicates only rely on the has_pred feature, so the map
can be kept or removed as a whole -}
pr_pred_map :: CASL_SL a -> Pred_map -> Pred_map
pr_pred_map l x = if has_pred l then x else Map.empty

pr_op_map :: Lattice a => CASL_SL a -> Op_map -> Op_map
pr_op_map = Map.filterWithKey . pr_op_map_entry

pr_op_map_entry :: Lattice a => CASL_SL a -> (Id, OpType) -> (Id, OpKind)
    -> Bool
pr_op_map_entry l (_, t) (_, b) =
    has_part l || in_x l t sl_optype && b == Partial

{- compute a morphism that consists of the original signature
and the projected signature -}
pr_epsilon :: m -> CASL_SL a -> Sign f e -> Morphism f e m
pr_epsilon extEm l s = embedMorphism extEm s $ pr_sign l s

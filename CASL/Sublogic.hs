{- |
Module      :  $Header$
Copyright   :  (c) Pascal Schmidt, C. Maeder, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs)
  for CASL. The functions allow to compute the minimal sublogics needed
  by a given element, to check whether an item is part of a given
  sublogic, and to project an element into a given sublogic.
-}

-- to do: implement pr_sign

module CASL.Sublogic ( -- * datatypes
                   CASL_Sublogics(..),
                   CASL_Formulas(..),
                   SubsortingFeatures(..),
                   SortGenerationFeatures(..),

                   -- * predicates on CASL_Sublogics
                   has_sub,
                   has_cons,

                   -- * functions for LatticeWithTop instance
                   top,
                   sublogics_max,
                   sublogics_min,

                   -- * functions for the creation of minimal sublogics
                   bottom,
                   need_sub,
                   need_sul,
                   need_part,
                   need_cons,
                   need_e_cons,
                   need_s_cons,
                   need_se_cons,
                   need_eq,
                   need_pred,
                   need_horn,
                   need_ghorn,
                   need_fol,
                   -- * functions for Logic instance

                   -- * sublogic to string conversion
                   sublogics_name,

                   -- * list of all sublogics
                   sublogics_all,

                   -- * checks if element is in given sublogic
                   in_basic_spec,
                   in_sentence,
                   in_symb_items,
                   in_symb_map_items,
                   in_sign,
                   in_morphism,
                   in_symbol,

                   -- * computes the sublogic of a given element
                   sl_basic_spec,
                   sl_sentence,
                   sl_symb_items,
                   sl_symb_map_items,
                   sl_sign,
                   sl_morphism,
                   sl_symbol,

                   -- * projects an element into a given sublogic
                   pr_basic_spec,
                   pr_symb_items,
                   pr_symb_map_items,
                   pr_sign,
                   pr_morphism,
                   pr_epsilon,
                   pr_symbol
                 ) where

import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Inject

------------------------------------------------------------------------------
-- | Datatypes for CASL sublogics
------------------------------------------------------------------------------

data CASL_Formulas = Atomic  -- ^ atomic logic
                   | Horn    -- ^ positive conditional logic
                   | GHorn   -- ^ generalized positive conditional logic
                   | FOL     -- ^ first-order logic
                   deriving (Show,Ord,Eq)

data SubsortingFeatures = NoSub
                        | LocFilSub
                        | Sub
                          deriving (Show,Ord,Eq)

data SortGenerationFeatures =
          NoSortGen
        | SortGen { emptyMapping :: Bool
                    -- ^ Mapping of indexed sorts is empty
                  , onlyInjConstrs :: Bool
                    -- ^ only injective constructors
                  } deriving (Show,Eq)

instance Ord SortGenerationFeatures where
  {-   NoSortGen False False > NoSortGen True False
     > NoSortGen False True  > NoSortGen True True -}
    compare x y =
        case x of
        NoSortGen -> case y of
                     NoSortGen -> EQ
                     _         -> LT
        SortGen em_x ojc_x ->
            case y of
            NoSortGen -> GT
            SortGen em_y ojc_y ->
                case (em_x,ojc_x,em_y,ojc_y) of
                -- False means more expressive / more features used
                (True,True,True,True)    -> EQ
                (True,True,False,True)   -> LT
                (True,True,True,False)   -> LT
                (True,True,False,False)  -> LT

                (True,False,True,True)   -> GT
                (True,False,True,False)  -> EQ
                (True,False,False,True)  -> GT
                (True,False,False,False) -> LT

                (False,True,True,True)   -> GT
                (False,True,True,False)  -> LT
                (False,True,False,False) -> LT
                (False,True,False,True)  -> EQ

                (False,False,True,True)  -> GT
                (False,False,True,False) -> GT
                (False,False,False,True) -> GT
                (False,False,False,False)-> EQ

data CASL_Sublogics = CASL_SL
                      { sub_features :: SubsortingFeatures, -- ^ subsorting
                        has_part::Bool,  -- ^ partiality
                        cons_features :: SortGenerationFeatures,
                            -- ^ sort generation constraints
                        has_eq::Bool,    -- ^ equality
                        has_pred::Bool,  -- ^ predicates
                        which_logic::CASL_Formulas
                      } deriving (Show,Eq)
-------------------------
-- old selector functions
-------------------------

has_sub :: CASL_Sublogics -> Bool
has_sub sl = case sub_features sl of
             NoSub -> False
             _ -> True

has_cons :: CASL_Sublogics -> Bool
has_cons sl = case cons_features sl of
              NoSortGen -> False
              _ -> True
-----------------------------------------------------------------------------
-- Special sublogics elements
-----------------------------------------------------------------------------

-- top element
--
top :: CASL_Sublogics
top = (CASL_SL LocFilSub True (SortGen True True) True True FOL)

-- bottom element
--
bottom :: CASL_Sublogics
bottom = (CASL_SL NoSub False (NoSortGen) False False Atomic)

-- the following are used to add a needed feature to a given
-- sublogic via sublogics_max, i.e. (sublogics_max given needs_part)
-- will force partiality in addition to what features given already
-- has included

-- minimal sublogics with subsorting
--
need_sub :: CASL_Sublogics
need_sub = bottom { sub_features = Sub, which_logic = Horn }

need_sul :: CASL_Sublogics
need_sul = bottom { sub_features = LocFilSub, which_logic = Horn }

-- minimal sublogic with partiality
--
need_part :: CASL_Sublogics
need_part = bottom { has_part = True }

-- minimal sublogics with sort generation constraints
--
need_cons :: CASL_Sublogics
need_cons = bottom { cons_features = SortGen { emptyMapping = False
                                             , onlyInjConstrs = False} }
need_e_cons :: CASL_Sublogics
need_e_cons = bottom { cons_features = SortGen { emptyMapping = True
                                               , onlyInjConstrs = False} }
need_s_cons :: CASL_Sublogics
need_s_cons = bottom { cons_features = SortGen { emptyMapping = False
                                               , onlyInjConstrs = True} }
need_se_cons :: CASL_Sublogics
need_se_cons = bottom { cons_features = SortGen { emptyMapping = True
                                                , onlyInjConstrs = True} }

-- minimal sublogic with equality
--
need_eq :: CASL_Sublogics
need_eq = bottom { has_eq = True }

-- minimal sublogic with predicates
--
need_pred :: CASL_Sublogics
need_pred = bottom { has_pred = True }

need_horn :: CASL_Sublogics
need_horn = bottom { which_logic = Horn }

need_ghorn :: CASL_Sublogics
need_ghorn = bottom { which_logic = GHorn }

need_fol :: CASL_Sublogics
need_fol = bottom { which_logic = FOL }

-----------------------------------------------------------------------------
-- Functions to generate a list of all sublogics for CASL
-----------------------------------------------------------------------------

-- all elements
-- create a list of all CASL sublogics by generating all possible
-- feature combinations and then filtering illegal ones out
--
sublogics_all :: [CASL_Sublogics]
sublogics_all =
    filter (not . adjust_check)
           [ CASL_SL s_f pa_b c_f e_b pr_b fo
                       | s_f <- [NoSub,LocFilSub,Sub ],
                         pa_b <- [True,False],
                         pr_b <- [True,False],
                         e_b <- [True,False],
                         fo <- [FOL,GHorn,Horn,Atomic],
                         c_f <- (NoSortGen:[SortGen m s | m <- [True,False],
                                                          s <- [True,False]])]
------------------------------------------------------------------------------
-- Conversion functions (to String)
------------------------------------------------------------------------------

formulas_name :: Bool -> CASL_Formulas -> String
formulas_name True  FOL    = "FOL"
formulas_name False FOL    = "FOAlg"
formulas_name True  GHorn  = "GHorn"
formulas_name False GHorn  = "GCond"
formulas_name True  Horn   = "Horn"
formulas_name False Horn   = "Cond"
formulas_name True  Atomic = "Atom"
formulas_name False Atomic = "Eq"

sublogics_name :: CASL_Sublogics -> [String]
sublogics_name x = [   ( case sub_features x of
                         NoSub     -> ""
                         LocFilSub -> "Sul"
                         Sub       -> "Sub")
                    ++ ( if (has_part x) then "P" else "")
                    ++ ( if (has_cons x)
                         then (  (if onlyInjConstrs (cons_features x)
                                  then "s" else "")
                               ++(if emptyMapping (cons_features x)
                                  then "e" else "")
                               ++"C")
                         else "")
                    ++ ( formulas_name (has_pred x) (which_logic x) )
                    ++ ( if (has_eq   x) then "=" else "")]

------------------------------------------------------------------------------
-- min/join and max/meet functions
------------------------------------------------------------------------------

sublogics_max :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_max a b = CASL_SL (max (sub_features a) (sub_features b))
                            (has_part a || has_part b)
                            (max (cons_features a) (cons_features b))
                            (has_eq   a || has_eq   b)
                            (has_pred a || has_pred b)
                            (max (which_logic a) (which_logic b))

sublogics_min :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_min a b = CASL_SL (min (sub_features a) (sub_features b))
                            (has_part a && has_part b)
                            (min (cons_features a) (cons_features b))
                            (has_eq   a && has_eq   b)
                            (has_pred a && has_pred b)
                            (min (which_logic a) (which_logic b))

instance Ord CASL_Sublogics where
  x <= y = sublogics_min x y == x

------------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------------

-- compute sublogics from a list of sublogics
--
comp_list :: [CASL_Sublogics] -> CASL_Sublogics
comp_list l = foldl sublogics_max bottom l

-- adjust illegal combination "subsorting with atomic logic"
--
adjust_logic :: CASL_Sublogics -> CASL_Sublogics
adjust_logic x = if (adjust_check x) then
                   x { which_logic = Horn }
                 else
                   x

-- check for illegal combination "subsorting with atomic logic"
--
adjust_check :: CASL_Sublogics -> Bool
adjust_check x = (has_sub x) && (which_logic x == Atomic)

-- map a function returning Maybe over a list of arguments
-- . a list of Pos is maintained by removing an element if the
--   function f returns Nothing on the corresponding element of
--   the argument list
-- . leftover elements in the Pos list after the argument
--   list is exhausted are appended at the end with Nothing
--   as a substitute for f's result
--
mapMaybePos :: [Pos] -> (a -> Maybe b) -> [a] -> [(Maybe b,Pos)]
mapMaybePos [] _ _          = []
mapMaybePos (p1:pl) f []    = (Nothing,p1):(mapMaybePos pl f [])
mapMaybePos (p1:pl) f (h:t) = let
                                res = f h
                              in
                                if (isJust res) then
                                  (res,p1):(mapMaybePos pl f t)
                                else
                                  mapMaybePos pl f t

-- map with partial function f on Maybe type
--  will remove elements from given Pos list for elements of [a]
--  where f returns Nothing
--  given number of elements from the beginning of Range are always
--  kept
--
mapPos :: Int -> Range -> (a -> Maybe b) -> [a] -> ([b],Range)
mapPos c (Range p) f l = let
                   (res,pos) = (\(x,y) -> (catMaybes x,y))
                               $ unzip $ mapMaybePos (drop c p) f l
                 in
                   (res,Range ((take c p)++pos))

------------------------------------------------------------------------------
-- Functions to analyse formulae
------------------------------------------------------------------------------

{- ---------------------------------------------------------------------------
   These functions are based on Till Mossakowski's paper "Sublanguages of
   CASL", which is CoFI Note L-7. The functions implement an adaption of
   the reduced grammar given there for formulae in a specific expression
   logic by, checking whether a formula would match the productions from the
   grammar. Which function checks for which nonterminal from the paper is
   given as a comment before each function.
--------------------------------------------------------------------------- -}

sl_form_level :: (Bool,Bool) -> FORMULA f -> CASL_Sublogics
sl_form_level (isCompound,leftImp) phi =
 case phi of
   Quantification q _ f _ ->
    if is_atomic_q q
    then sl_form_level (isCompound,leftImp) f
    else need_fol
   Conjunction l _ -> comp_list $ map (sl_form_level (True,leftImp)) l
   Disjunction _ _ -> need_fol
   Implication l1 l2 _ _ -> if leftImp then need_fol else
               comp_list [sl_form_level (True,True) l1,
                   sl_form_level (True,False) l2,
                   if isCompound
                   then need_ghorn
                   else need_horn]
   Equivalence l1 l2 _ ->
    if leftImp
    then need_fol
    else comp_list [sl_form_level (True,True) l1,
                    sl_form_level (True,True) l2,
                    need_ghorn]
   Negation _ _ -> need_fol -- it won't get worse
   True_atom _ -> bottom
   False_atom _ -> need_fol
   Predication _ _ _ -> bottom
   Definedness _ _ -> bottom
   Existl_equation _ _ _ -> bottom
   Strong_equation _ _ _ -> if leftImp then need_fol else need_horn
   Membership _ _ _ -> bottom
   Sort_gen_ax _ _ -> bottom
   _ -> error "CASL.Sublogic.sl_form_level: illegal FORMULA type"


-- QUANTIFIER
--
is_atomic_q :: QUANTIFIER -> Bool
is_atomic_q (Universal) = True
is_atomic_q _ = False

-- compute logic of a formula by checking all logics in turn
--
get_logic :: FORMULA f -> CASL_Sublogics
get_logic = sl_form_level (False,False)

-- for the formula inside a subsort-defn
--
get_logic_sd :: FORMULA f -> CASL_Sublogics
get_logic_sd f = sublogics_max need_horn $ sl_form_level (False,False) f
{- get_logic_sd f = if (is_horn_p_a f) then need_horn else
                 if (is_ghorn_prem f) then need_ghorn else
                 need_fol -}

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element, these work
-- by recursing into all subelements
------------------------------------------------------------------------------

sl_basic_spec :: BASIC_SPEC b s f -> CASL_Sublogics
sl_basic_spec (Basic_spec l) = comp_list $ map sl_basic_items
                                         $ map item l

sl_basic_items :: BASIC_ITEMS b s f -> CASL_Sublogics
sl_basic_items (Sig_items i) = sl_sig_items i
sl_basic_items (Free_datatype l _) = comp_list $ map sl_datatype_decl
                                               $ map item l
sl_basic_items (Sort_gen l _) = sublogics_max need_cons
                                (comp_list $ map sl_sig_items
                                           $ map item l)
sl_basic_items (Var_items l _) = comp_list $ map sl_var_decl l
sl_basic_items (Local_var_axioms d l _) = sublogics_max
                                          (comp_list $ map sl_var_decl d)
                                          (comp_list $ map sl_formula
                                                     $ map item l)
sl_basic_items (Axiom_items l _) = comp_list $ map sl_formula
                                             $ map item l
sl_basic_items _ = error "CASL.Sublogic.sl_basic_items"

sl_sig_items :: SIG_ITEMS s f -> CASL_Sublogics
sl_sig_items (Sort_items l _) = comp_list $ map sl_sort_item $ map item l
sl_sig_items (Op_items l _) = comp_list $ map sl_op_item $ map item l
sl_sig_items (Pred_items l _) = comp_list $ map sl_pred_item $ map item l
sl_sig_items (Datatype_items l _) = comp_list $ map sl_datatype_decl
                                              $ map item l
sl_sig_items _ = error "CASL.Sublogic.sl_sig_items"

-- Subsort_defn needs to compute the expression logic needed seperately
-- because the expressiveness allowed in the formula may be different
-- from more general formulae in the same expression logic
--
sl_sort_item :: SORT_ITEM f -> CASL_Sublogics
sl_sort_item (Subsort_decl _ _ _) = need_sub
sl_sort_item (Subsort_defn _ _ _ f _) = sublogics_max
                                        (get_logic_sd $ item f)
                                        (sublogics_max need_sub
                                        (sl_formula $ item f))
sl_sort_item (Iso_decl _ _) = need_sub
sl_sort_item _ = bottom

sl_op_item :: OP_ITEM f -> CASL_Sublogics
sl_op_item (Op_decl _ t l _) = sublogics_max (sl_op_type t)
                               (comp_list $ map sl_op_attr l)
sl_op_item (Op_defn _ h t _) = sublogics_max (sl_op_head h)
                                             (sl_term $ item t)

sl_op_attr :: OP_ATTR f -> CASL_Sublogics
sl_op_attr (Unit_op_attr t) = sl_term t
sl_op_attr _ = need_eq

sl_op_type :: OP_TYPE -> CASL_Sublogics
sl_op_type (Op_type Partial _ _ _) = need_part
sl_op_type _ = bottom

sl_op_head :: OP_HEAD -> CASL_Sublogics
sl_op_head (Op_head Partial _ _ _) = need_part
sl_op_head _ = bottom

sl_pred_item :: PRED_ITEM f -> CASL_Sublogics
sl_pred_item (Pred_decl _ _ _) = need_pred
sl_pred_item (Pred_defn _ _ f _) = sublogics_max need_pred
                                                 (sl_formula $ item f)

sl_datatype_decl :: DATATYPE_DECL -> CASL_Sublogics
sl_datatype_decl (Datatype_decl _ l _) = comp_list $ map sl_alternative
                                                   $ map item l

sl_alternative :: ALTERNATIVE -> CASL_Sublogics
sl_alternative (Alt_construct Total _ l _) =  comp_list $ map sl_components l
sl_alternative (Alt_construct Partial _ _ _) = need_part
sl_alternative (Subsorts _ _) = need_sub

sl_components :: COMPONENTS -> CASL_Sublogics
sl_components (Cons_select Partial _ _ _) = need_part
sl_components _ = bottom

sl_var_decl :: VAR_DECL -> CASL_Sublogics
sl_var_decl _ = bottom

{- without subsorts casts are trivial and would not even require
   need_part, but testing term_sort is not save for formulas in basic specs
   that are only parsed (and resolved) but not enriched with sorts -}
sl_term :: TERM f -> CASL_Sublogics
-- the subterms may make it worse than "need_part"
sl_term (Cast t _ _) = sublogics_max need_part $ sl_term t
-- check here also for the formula_level!
sl_term (Conditional t f u _) = comp_list [sl_term t,sl_formula f,sl_term u]
sl_term (Sorted_term t _ _) = sl_term t
sl_term (Application _ l _) = comp_list $ map sl_term l
sl_term (Qual_var _ _ _) = bottom
sl_term _ = error "CASL.Sublogic.sl_term"

sl_formula :: FORMULA f -> CASL_Sublogics
sl_formula f = sublogics_max (get_logic f) (sl_form f)

sl_form :: FORMULA f -> CASL_Sublogics
sl_form (Quantification _ _ f _) = sl_form f
sl_form (Conjunction l _) = comp_list $ map sl_form l
sl_form (Disjunction l _) = comp_list $ map sl_form l
sl_form (Implication f g _ _) = sublogics_max (sl_form f) (sl_form g)
sl_form (Equivalence f g _) = sublogics_max (sl_form f) (sl_form g)
sl_form (Negation f _) = sl_form f
sl_form (True_atom _) = bottom
sl_form (False_atom _) = bottom
sl_form (Predication _ l _) = sublogics_max need_pred
                              (comp_list $ map sl_term l)
-- need_part is tested elsewhere (need_pred not required)
sl_form (Definedness t _) = sl_term t
sl_form (Existl_equation t u _) = comp_list [need_eq,sl_term t,sl_term u]
sl_form (Strong_equation t u _) = comp_list [need_eq,sl_term t,sl_term u]
-- need_sub is tested elsewhere (need_pred not required)
sl_form (Membership t _ _) = sl_term t
sl_form (Sort_gen_ax constraints _) =
    case recover_Sort_gen_ax constraints of
    (_,ops,mapping)
        | null mapping && null otherConstrs       -> need_se_cons
        | null mapping && not (null otherConstrs) -> need_e_cons
        | not (null mapping) && null otherConstrs -> need_s_cons
        | otherwise                               -> need_cons
       where otherConstrs =
                 filter (\ o -> case o of
                                Op_name _ ->
                                    error "CASL.Sublogic.sl_form: Wrong \
                                          \OP_SYMB constructor."
                                Qual_op_name n _ _ -> n /= injName) ops

sl_form _ = error "CASL.Sublogic.sl_form"

sl_symb_items :: SYMB_ITEMS -> CASL_Sublogics
sl_symb_items (Symb_items k l _) = sublogics_max (sl_symb_kind k)
                                   (comp_list $ map sl_symb l)

sl_symb_kind :: SYMB_KIND -> CASL_Sublogics
sl_symb_kind (Preds_kind) = need_pred
sl_symb_kind _ = bottom

sl_symb :: SYMB -> CASL_Sublogics
sl_symb (Symb_id _) = bottom
sl_symb (Qual_id _ t _) = sl_type t

sl_type :: TYPE -> CASL_Sublogics
sl_type (O_type t) = sl_op_type t
sl_type (P_type _) = need_pred
sl_type _ = bottom

sl_symb_map_items :: SYMB_MAP_ITEMS -> CASL_Sublogics
sl_symb_map_items (Symb_map_items k l _) = sublogics_max (sl_symb_kind k)
                                          (comp_list $ map sl_symb_or_map l)

sl_symb_or_map :: SYMB_OR_MAP -> CASL_Sublogics
sl_symb_or_map (Symb s) = sl_symb s
sl_symb_or_map (Symb_map s t _) = sublogics_max (sl_symb s) (sl_symb t)

-- the maps have no influence since all sorts,ops,preds in them
-- must also appear in the signatures, so any features needed by
-- them will be included by just checking the signatures
--

sl_sign :: Sign f e -> CASL_Sublogics
sl_sign s =
    let subs = if Rel.null (sortRel s)
               then bottom
               else if Rel.locallyFiltered (sortRel s)
                    then need_sul
                    else need_sub
        preds = if Map.null $ predMap s then bottom else need_pred
        partial = if any ( \ t -> opKind t == Partial) $ Set.toList
                  $ Set.unions $ Map.elems $ opMap s then need_part else bottom
        in sublogics_max subs (sublogics_max preds partial)

sl_sentence :: FORMULA f -> CASL_Sublogics
sl_sentence = sl_formula

sl_morphism :: Morphism f e m -> CASL_Sublogics
sl_morphism m = sublogics_max (sl_sign $ msource m) (sl_sign $ mtarget m)

sl_symbol :: Symbol -> CASL_Sublogics
sl_symbol (Symbol _ t) = sl_symbtype t

sl_symbtype :: SymbType -> CASL_Sublogics
sl_symbtype (OpAsItemType t) = sl_optype t
sl_symbtype (PredAsItemType _) = need_pred
sl_symbtype _ = bottom

sl_optype :: OpType -> CASL_Sublogics
sl_optype k = sl_funkind $ opKind k

sl_funkind :: FunKind -> CASL_Sublogics
sl_funkind (Partial) = need_part
sl_funkind _ = bottom

------------------------------------------------------------------------------
-- comparison functions
------------------------------------------------------------------------------

-- negated implication
--
nimpl :: Bool -> Bool -> Bool
nimpl True _      = True
nimpl False False = True
nimpl False True  = False

-- check if a "new" sublogic is contained in/equal to a given
-- sublogic
--
sl_in :: CASL_Sublogics -> CASL_Sublogics -> Bool
sl_in given new = (nimpl (has_sub  given) (has_sub  new)) &&
                  (nimpl (has_part given) (has_part new)) &&
                  (nimpl (has_cons given) (has_cons new)) &&
                  (nimpl (has_eq   given) (has_eq   new)) &&
                  (nimpl (has_pred given) (has_pred new)) &&
                  ((which_logic given) >= (which_logic new))

in_x :: CASL_Sublogics -> a -> (a -> CASL_Sublogics) -> Bool
in_x l x f = sl_in l (f x)

in_basic_spec :: CASL_Sublogics -> BASIC_SPEC b s f -> Bool
in_basic_spec l x = in_x l x sl_basic_spec

in_sentence :: CASL_Sublogics -> FORMULA f -> Bool
in_sentence l x = in_x l x sl_sentence

in_symb_items :: CASL_Sublogics -> SYMB_ITEMS -> Bool
in_symb_items l x = in_x l x sl_symb_items

in_symb_map_items :: CASL_Sublogics -> SYMB_MAP_ITEMS -> Bool
in_symb_map_items l x = in_x l x sl_symb_map_items

in_sign :: CASL_Sublogics -> Sign f e -> Bool
in_sign l x = in_x l x sl_sign

in_morphism :: CASL_Sublogics -> Morphism f e m -> Bool
in_morphism l x = in_x l x sl_morphism

in_symbol :: CASL_Sublogics -> Symbol -> Bool
in_symbol l x = in_x l x sl_symbol

------------------------------------------------------------------------------
-- projection functions
------------------------------------------------------------------------------

-- process Annoted type like simple type, simply keep all annos
--
pr_annoted :: CASL_Sublogics -> (CASL_Sublogics -> a -> Maybe a)
              -> Annoted a -> Maybe (Annoted a)
pr_annoted sl f a = let
                      res = f sl (item a)
                    in
                      if (isNothing res) then
                        Nothing
                    else
                      Just (a { item = fromJust res })

-- project annoted type, by-producing a [SORT]
-- used for projecting datatypes: sometimes it is necessary to
-- introduce a SORT_DEFN for a datatype that was erased
-- completely, for example by only having partial constructors
-- and partiality forbidden in the desired sublogic - the sort
-- name may however still be needed for formulas because it can
-- appear there like in (forall x,y:Datatype . x=x), a formula
-- that does not use partiality (does not use any constructor
-- or selector)
--
pr_annoted_dt :: CASL_Sublogics -> (CASL_Sublogics -> a -> (Maybe a,[SORT]))
                 -> Annoted a -> (Maybe (Annoted a),[SORT])
pr_annoted_dt sl f a = let
                         (res,lst) = f sl (item a)
                       in
                         if (isNothing res) then
                           (Nothing,lst)
                         else
                           (Just (a { item = fromJust res }),lst)

-- keep an element if its computed sublogic is in the given sublogic
--
pr_check :: CASL_Sublogics -> (a -> CASL_Sublogics) -> a -> Maybe a
pr_check l f e = if (in_x l e f) then (Just e) else Nothing

pr_formula :: CASL_Sublogics -> FORMULA f -> Maybe (FORMULA f)
pr_formula l f = pr_check l sl_formula f

-- make full Annoted Sig_items out of a SORT list
--
pr_make_sorts :: [SORT] -> Annoted (BASIC_ITEMS b s f)
pr_make_sorts s =
  Annoted (Sig_items (Sort_items
             [Annoted (Sort_decl s nullRange) nullRange [][]]
             nullRange))
          nullRange [][]

-- when processing BASIC_SPEC, add a Sort_decl in front for sorts
-- defined by DATATYPE_DECLs that had to be removed completely,
-- otherwise formulas might be broken by the missing sorts, thus
-- breaking the projection
--
pr_basic_spec :: CASL_Sublogics -> BASIC_SPEC b s f -> BASIC_SPEC b s f
pr_basic_spec l (Basic_spec s) =
  let
    res   = map (pr_annoted_dt (adjust_logic l) pr_basic_items) s
    items = catMaybes $ map fst res
    toAdd = concat $ map snd res
    ret   = if (toAdd==[]) then
              items
            else
              (pr_make_sorts toAdd):items
  in
    Basic_spec ret

-- returns a non-empty list of [SORT] if datatypes had to be removed
-- completely
--
pr_basic_items :: CASL_Sublogics -> BASIC_ITEMS b s f
                   -> (Maybe (BASIC_ITEMS b s f), [SORT])
pr_basic_items l (Sig_items s) =
               let
                 (res,lst) = pr_sig_items l s
               in
                 if (isNothing res) then
                   (Nothing,lst)
                 else
                   (Just (Sig_items (fromJust res)),lst)
pr_basic_items l (Free_datatype d p) =
               let
                 (res,pos) = mapPos 2 p (pr_annoted l pr_datatype_decl) d
                 lst       = pr_lost_dt l (map item d)
               in
                 if (null res) then
                   (Nothing,lst)
                 else
                   (Just (Free_datatype res pos),lst)
pr_basic_items l (Sort_gen s p) =
               if (has_cons l) then
                 let
                   tmp = map (pr_annoted_dt l pr_sig_items) s
                   res = catMaybes $ map fst tmp
                   lst = concat $ map snd tmp
                 in
                   if (null res) then
                     (Nothing,lst)
                   else
                     (Just (Sort_gen res p),lst)
               else
                 (Nothing,[])
pr_basic_items _ (Var_items v p) = (Just (Var_items v p),[])
pr_basic_items l (Local_var_axioms v f p) =
               let
                 (res,pos) = mapPos (length v) p (pr_annoted l pr_formula) f
               in
                 if (null res) then
                   (Nothing,[])
                 else
                   (Just (Local_var_axioms v res pos),[])
pr_basic_items l (Axiom_items f p) =
               let
                 (res,pos) = mapPos 0 p (pr_annoted l pr_formula) f
               in
                 if (null res) then
                   (Nothing,[])
                 else
                   (Just (Axiom_items res pos),[])
pr_basic_items _ _ = error "CASL.Sublogic.pr_basic_items"

pr_datatype_decl :: CASL_Sublogics -> DATATYPE_DECL -> Maybe DATATYPE_DECL
pr_datatype_decl l (Datatype_decl s a p) =
                 let
                   (res,pos) = mapPos 1 p (pr_annoted l pr_alternative) a
                 in
                   if (null res) then
                     Nothing
                   else
                     Just (Datatype_decl s res pos)


pr_alternative :: CASL_Sublogics -> ALTERNATIVE -> Maybe ALTERNATIVE
pr_alternative l (Alt_construct Total n c p) =
               let
                 (res,pos) = mapPos 1 p (pr_components l) c
               in
                 if (null res) then
                   Nothing
                 else
                   Just (Alt_construct Total n res pos)
pr_alternative l alt@(Alt_construct Partial _ _ _) =
             if ((has_part l)==True) then
               Just alt
             else
               Nothing
pr_alternative l (Subsorts s p) =
               if ((has_sub l)==True) then
                 Just (Subsorts s p)
               else
                 Nothing

pr_components :: CASL_Sublogics -> COMPONENTS -> Maybe COMPONENTS
pr_components l sel@(Cons_select Partial _ _ _) =
              if ((has_part l)==True) then
                Just sel
              else
                Nothing
pr_components _ x = Just x

-- takes a list of datatype declarations and checks whether a
-- whole declaration is invalid in the given sublogic - if this
-- is the case, the sort that would be declared by the type is
-- added to a list of SORT that is emitted
--
pr_lost_dt :: CASL_Sublogics -> [DATATYPE_DECL] -> [SORT]
pr_lost_dt _ [] = []
pr_lost_dt sl ((Datatype_decl s l p):t) =
                     let
                       res = pr_datatype_decl sl (Datatype_decl s l p)
                     in
                       if (isNothing res) then
                         s:(pr_lost_dt sl t)
                       else
                         pr_lost_dt sl t

pr_symbol :: CASL_Sublogics -> Symbol -> Maybe Symbol
pr_symbol l s = pr_check l sl_symbol s

-- returns a non-empty list of [SORT] if datatypes had to be removed
-- completely
--
pr_sig_items :: CASL_Sublogics -> SIG_ITEMS s f
                -> (Maybe (SIG_ITEMS s f),[SORT])
pr_sig_items l (Sort_items s p) =
             let
               (res,pos) = mapPos 1 p (pr_annoted l pr_sort_item) s
             in
               if (null res) then
                 (Nothing,[])
               else
                 (Just (Sort_items res pos),[])
pr_sig_items l (Op_items o p) =
             let
               (res,pos) = mapPos 1 p (pr_annoted l pr_op_item) o
             in
               if (null res) then
                 (Nothing,[])
               else
                 (Just (Op_items res pos),[])
pr_sig_items l (Pred_items i p) =
             if (has_pred l) then
               (Just (Pred_items i p),[])
             else
               (Nothing,[])
pr_sig_items l (Datatype_items d p) =
             let
               (res,pos) = mapPos 1 p (pr_annoted l pr_datatype_decl) d
               lst       = pr_lost_dt l (map item d)
             in
               if (null res) then
                 (Nothing,lst)
               else
                 (Just (Datatype_items res pos),lst)
pr_sig_items _ _ = error "CASL.Sublogic.pr_sig_items"

pr_op_item :: CASL_Sublogics -> OP_ITEM f -> Maybe (OP_ITEM f)
pr_op_item l i = pr_check l sl_op_item i

-- subsort declarations and definitions are reduced to simple
-- sort declarations if the sublogic disallows subsorting to
-- avoid loosing sorts in the projection
--
pr_sort_item ::
                CASL_Sublogics -> SORT_ITEM f -> Maybe (SORT_ITEM f)
pr_sort_item _ (Sort_decl s p) = Just (Sort_decl s p)
pr_sort_item l (Subsort_decl sl s p) =
             if (has_sub l) then
               Just (Subsort_decl sl s p)
             else
               Just (Sort_decl (s:sl) nullRange)
pr_sort_item l (Subsort_defn s1 v s2 f p) =
             if (has_sub l) then
               Just (Subsort_defn s1 v s2 f p)
             else
               Just (Sort_decl [s1] nullRange)
pr_sort_item _ (Iso_decl s p) = Just (Iso_decl s p)

pr_symb_items :: CASL_Sublogics -> SYMB_ITEMS -> Maybe SYMB_ITEMS
pr_symb_items l1 (Symb_items k s p) =
            let
              l = adjust_logic l1
            in
              if (in_x l k sl_symb_kind) then
                let
                  (res,pos) = mapPos 1 p (pr_symb l) s
                in
                  if (null res) then
                    Nothing
                  else
                    Just (Symb_items k res pos)
              else
                Nothing

pr_symb_map_items :: CASL_Sublogics -> SYMB_MAP_ITEMS -> Maybe SYMB_MAP_ITEMS
pr_symb_map_items l1 (Symb_map_items k s p) =
                let
                  l = adjust_logic l1
                in
                  if (in_x l k sl_symb_kind) then
                    let
                      (res,pos) = mapPos 1 p (pr_symb_or_map l) s
                    in
                      if (null res) then
                        Nothing
                      else
                        Just (Symb_map_items k res pos)
                  else
                    Nothing

pr_symb_or_map :: CASL_Sublogics -> SYMB_OR_MAP -> Maybe SYMB_OR_MAP
pr_symb_or_map l (Symb s) =
               let
                 res = pr_symb l s
               in
                 if (isNothing res) then
                   Nothing
                 else
                   Just (Symb (fromJust res))
pr_symb_or_map l (Symb_map s t p) =
               let
                 a = pr_symb l s
                 b = pr_symb l t
               in
                 if ((isJust a) && (isJust b)) then
                   Just (Symb_map s t p)
                 else
                   Nothing

pr_symb :: CASL_Sublogics -> SYMB -> Maybe SYMB
pr_symb _ (Symb_id i) = Just (Symb_id i)
pr_symb l (Qual_id i t p) =
        if (in_x l t sl_type) then
          Just (Qual_id i t p)
        else
          Nothing

pr_sign :: CASL_Sublogics -> Sign f e -> Sign f e
pr_sign _sl s = s -- do something here

pr_morphism :: CASL_Sublogics -> Morphism f e m -> Morphism f e m
pr_morphism l1 m =
  let
    l = adjust_logic l1
  in m { msource = pr_sign l $ msource m
       , mtarget = pr_sign l $ mtarget m
       , fun_map = pr_fun_map l $ fun_map m
       , pred_map = pr_pred_map l $ pred_map m }

-- predicates only rely on the has_pred feature, so the map
-- can be kept or removed as a whole
--
pr_pred_map :: CASL_Sublogics -> Pred_map -> Pred_map
pr_pred_map l x = if (has_pred l) then x else Map.empty

pr_fun_map :: CASL_Sublogics -> Fun_map -> Fun_map
pr_fun_map l m = Map.filterWithKey (pr_fun_map_entry l) m

pr_fun_map_entry :: CASL_Sublogics -> (Id, OpType) -> (Id, FunKind) -> Bool
pr_fun_map_entry l (_,t) (_,b) =
                 if (has_part l) then True
                 else ((in_x l t sl_optype) && b == Partial)

-- compute a morphism that consists of the original signature
-- and the projected signature
--
pr_epsilon :: Ext f e m -> CASL_Sublogics -> Sign f e -> Morphism f e m
pr_epsilon extEm l1 s = let
                    l = adjust_logic l1
                    new = pr_sign l s
                  in
                    embedMorphism extEm new s

------------------------------------------------------------------------------
-- HetCATS/CASL/Sublogics.hs
-- $Id$
-- Authors: Pascal Schmidt
-- Year:    2002
------------------------------------------------------------------------------
{- todo:

  [Pos] in LocalEnv.SortDefn -> Christian Maeder fragen
  What if Datatype is removed (only situation where a sort can be removed
  entirely) but preds or Sort_map still exist?  -> in Sort_decl umwandeln

  all_sublogics :: id -> [sublogics]
  Sublogic ggf. hochsetzen (für subsorted atomic logic)
  Morphism umstellen, in Zusammenarbeit mit Klaus

  in eignem File:
  Hochziehen auf strukturierte Ebene
    Maybe(existentiellen Typ G_sublogics aus Grothendieck.hs) verwenden
    AS_Structured.hs, AS_Arch.hs, AS_Library.hs
    Funktionen aus Logic_CASL.hs bzw. Logic.hs verwenden
    Nur für homogene Specs das jeweilige Maximum berechnen
      (Vergleich von Logic-ids mit language_name), ansonsten Nothing

  Testen mit hetcats/hetcats.hs (Klaus kontakten)

-}

module Sublogics where

import Maybe
import FiniteMap
import Id
import AS_Annotation
import AS_Basic_CASL
import LocalEnv

------------------------------------------------------------------------------
-- datatypes for CASL sublogics
------------------------------------------------------------------------------

data CASL_Formulas = Atomic  -- atomic logic
                   | Horn    -- positive conditional logic
                   | GHorn   -- generalized positive conditional logic
                   | FOL     -- first-order logic
                   deriving (Show,Ord,Eq)

data CASL_Sublogics = CASL_SL
                      { has_sub::Bool,   -- subsorting
                        has_part::Bool,  -- partiality
                        has_cons::Bool,  -- sort generation contraints
                        has_eq::Bool,    -- equality
                        has_pred::Bool,  -- predicates
                        which_logic::CASL_Formulas
                      } deriving (Show,Ord,Eq)

-- top element
top :: CASL_Sublogics
top = (CASL_SL True True True True True FOL)

-- bottom element
bottom :: CASL_Sublogics
bottom = (CASL_SL False False False False False Atomic)

------------------------------------------------------------------------------
-- special constants
------------------------------------------------------------------------------

need_sub :: CASL_Sublogics
need_sub = (CASL_SL True False False False False Horn)

need_part :: CASL_Sublogics
need_part = (CASL_SL False True False False False Atomic)

need_cons :: CASL_Sublogics
need_cons = (CASL_SL False False True False False Atomic)

need_eq :: CASL_Sublogics
need_eq = (CASL_SL False False False True False Atomic)

need_pred :: CASL_Sublogics
need_pred = (CASL_SL False False False False True Atomic)

need_horn :: CASL_Sublogics
need_horn = (CASL_SL False False False False False Horn)

need_ghorn :: CASL_Sublogics
need_ghorn = (CASL_SL False False False False False GHorn)

need_fol :: CASL_Sublogics
need_fol = (CASL_SL False False False False False FOL)

------------------------------------------------------------------------------
-- conversion to String
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
sublogics_name x = [( if (has_sub x) then "Sub" else "" ) ++
                    ( if (has_part x) then "P" else "") ++
                    ( if (has_cons x) then "C" else "") ++
                    ( formulas_name (has_pred x) (which_logic x) ) ++
                    ( if (has_eq x) then "=" else "")]

------------------------------------------------------------------------------
-- min and max functions
------------------------------------------------------------------------------

formulas_max :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_max x y = if (x<y) then y else x

formulas_min :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_min x y = if (x<y) then x else y

sublogics_max :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_max (CASL_SL a1 b1 c1 d1 e1 l1) (CASL_SL a2 b2 c2 d2 e2 l2)
              = (CASL_SL (a1 || a2) (b1 || b2) (c1 || c2) (d1 || d2)
                 (e1 || e2) (formulas_max l1 l2))

sublogics_min :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_min (CASL_SL a1 b1 c1 d1 e1 l1) (CASL_SL a2 b2 c2 d2 e2 l2)
              = (CASL_SL (a1 && a2) (b1 && b2) (c1 && c2) (d1 && d2)
                 (e1 && e2) (formulas_min l1 l2))

------------------------------------------------------------------------------
-- helper functions
------------------------------------------------------------------------------

strip_anno :: Annoted a -> a
strip_anno (Annoted i _ _ _) = i

comp_list_helper :: CASL_Sublogics -> [CASL_Sublogics] -> CASL_Sublogics
comp_list_helper x []    = x
comp_list_helper x (h:t) = comp_list_helper (sublogics_max x h) t

comp_list :: [CASL_Sublogics] -> CASL_Sublogics
comp_list l = comp_list_helper bottom l

mb :: (a -> CASL_Sublogics) -> Maybe a -> CASL_Sublogics
mb f Nothing = bottom
mb f (Just x) = f x

-- adjust illegal combination "subsorting with atomic logic"
adjust_logic :: CASL_Sublogics -> CASL_Sublogics
adjust_logic x = if ((has_sub x) && (which_logic x == Atomic)) then
                   sublogics_max need_horn x
                 else
                   x

mapMaybePos :: [Pos] -> (a -> Maybe b) -> [a] -> [Pos]
mapMaybePos [] f l = []
mapMaybePos p f [] = p
mapMaybePos (p1:pl) f (h:t) = if (isJust (f h)) then
                                p1:(mapMaybePos pl f t)
                              else
                                mapMaybePos pl f t

-- tl n times if possible
tln :: Int -> [a] -> [a]
tln 0 l     = l
tln n []    = []
tln n (h:t) = tln (n-1) t

-- top n elements if possible
topn :: Int -> [a] -> [a]
topn 0 l     = []
topn n []    = []
topn n (h:t) = h:(topn (n-1) t)

mapPos :: [Pos] -> (a -> Maybe b) -> [a] -> ([b],[Pos])
mapPos p f l = let
                 res = mapMaybe f l
                 pos = mapMaybePos p f l
               in
                 (res,pos)

------------------------------------------------------------------------------
-- functions to analyse formulae
------------------------------------------------------------------------------

is_atomic_f :: FORMULA -> Bool
is_atomic_f (Quantification q _ f _) = (is_atomic_q q) && (is_atomic_f f)
is_atomic_f (Conjunction l _) = and ((map is_atomic_f) l)
is_atomic_f (True_atom _) = True
is_atomic_f (Predication _ _ _) = True
is_atomic_f (Definedness _ _) = True
is_atomic_f (Existl_equation _ _ _) = True
is_atomic_f _ = False

is_atomic_q :: QUANTIFIER -> Bool
is_atomic_q (Universal) = True
is_atomic_q _ = False

is_horn_f :: FORMULA -> Bool
is_horn_f (Quantification q _ f _) = (is_atomic_q q) && (is_horn_f f)
is_horn_f (Implication f g _) = (is_horn_p_conj f) && (is_horn_a g)
is_horn_f _ = False

is_horn_p_conj :: FORMULA -> Bool
is_horn_p_conj (Conjunction l _) = and ((map is_horn_p_a) l)
is_horn_p_conj _ = False

is_horn_a :: FORMULA -> Bool
is_horn_a (True_atom _) = True
is_horn_a (Predication _ _ _) = True
is_horn_a (Definedness _ _) = True
is_horn_a (Existl_equation _ _ _) = True
is_horn_a (Strong_equation _ _ _) = True
is_horn_a (Membership _ _ _) = True
is_horn_a _ = False

is_horn_p_a :: FORMULA -> Bool
is_horn_p_a (True_atom _) = True
is_horn_p_a (Predication _ _ _) = True
is_horn_p_a (Definedness _ _) = True
is_horn_p_a (Existl_equation _ _ _) = True
is_horn_p_a (Membership _ _ _) = True
is_horn_p_a _ = False

is_ghorn_f :: FORMULA -> Bool
is_ghorn_f (Quantification q _ f _) = (is_atomic_q q) && (is_ghorn_f f)
is_ghorn_f (Conjunction l _) = (is_ghorn_c_conj l) || (is_ghorn_f_conj l)
is_ghorn_f (Implication f g _) = (is_ghorn_prem f) && (is_ghorn_conc g)
is_ghorn_f (Equivalence f g _) = (is_ghorn_prem f) && (is_ghorn_prem g)
is_ghorn_f (True_atom _) = True
is_ghorn_f (Predication _ _ _) = True
is_ghorn_f (Definedness _ _) = True
is_ghorn_f (Existl_equation _ _ _) = True
is_ghorn_f (Strong_equation _ _ _) = True
is_ghorn_f (Membership _ _ _) = True
is_ghorn_f _ = False

is_ghorn_c_conj :: [FORMULA] -> Bool
is_ghorn_c_conj l = and ((map is_ghorn_conc) l)

is_ghorn_f_conj :: [FORMULA] -> Bool
is_ghorn_f_conj l = and ((map is_ghorn_f) l)

is_ghorn_p_conj :: [FORMULA] -> Bool
is_ghorn_p_conj l = and ((map is_ghorn_prem) l)

is_ghorn_prem :: FORMULA -> Bool
is_ghorn_prem (Conjunction l _) = is_ghorn_p_conj l
is_ghorn_prem x = is_horn_p_a x

is_ghorn_conc :: FORMULA -> Bool
is_ghorn_conc (Conjunction l _) = is_ghorn_c_conj l
is_ghorn_conc x = is_horn_a x

get_logic :: FORMULA -> CASL_Sublogics
get_logic f = if (is_atomic_f f) then bottom else
              if (is_horn_f f) then need_horn else
              if (is_ghorn_f f) then need_ghorn else
              need_fol

-- for the formula inside a subsort-defn
get_logic_sd :: FORMULA -> CASL_Sublogics
get_logic_sd f = if (is_horn_p_a f) then need_horn else
                 if (is_ghorn_prem f) then need_ghorn else
                 need_fol

-- and now for Formula instead of FORMULA

is_Atomic_f :: Formula -> Bool
is_Atomic_f (Quantified q _ f _) = (is_Atomic_q q) && (is_Atomic_f f)
is_Atomic_f (Connect AndOp l _) = and ((map is_Atomic_f) l)
is_Atomic_f (TrueAtom _) = True
is_Atomic_f (PredAppl _ _ _ _ _) = True
is_Atomic_f (TermTest ExEqualOp _ _) = True
is_Atomic_f (TermTest DefOp _ _) = True
is_Atomic_f (AnnFormula f) = is_Atomic_f (strip_anno f)
is_Atomic_f _ = False

is_Atomic_q :: Quantifier -> Bool
is_Atomic_q (Forall) = True
is_Atomic_q _ = False

is_Horn_f :: Formula -> Bool
is_Horn_f (Quantified q _ f _) = (is_Atomic_q q) && (is_Horn_f f)
is_Horn_f (Connect ImplOp [f,g] _) = (is_Horn_p_conj f) && (is_Horn_a g)
is_Horn_f (Connect IfOp [g,f] _) = (is_Horn_p_conj f) && (is_Horn_a g) 
is_Horn_f (AnnFormula f) = is_Horn_f (strip_anno f)
is_Horn_f _ = False

is_Horn_p_conj :: Formula -> Bool
is_Horn_p_conj (Connect AndOp l _) = and ((map is_Horn_p_a) l)
is_Horn_p_conj (AnnFormula f) = is_Horn_p_conj (strip_anno f)
is_Horn_p_conj _ = False

is_Horn_a :: Formula -> Bool
is_Horn_a (TrueAtom _) = True
is_Horn_a (PredAppl _ _ _ _ _) = True
is_Horn_a (TermTest _ _ _) = True
is_Horn_a (ElemTest _ _ _) = True
is_Horn_a (AnnFormula f) = is_Horn_a (strip_anno f)
is_Horn_a _ = False

is_Horn_p_a :: Formula -> Bool
is_Horn_p_a (TrueAtom _) = True
is_Horn_p_a (PredAppl _ _ _ _ _) = True
is_Horn_p_a (TermTest DefOp _ _) = True
is_Horn_p_a (TermTest ExEqualOp _ _) = True
is_Horn_p_a (ElemTest _ _ _) = True
is_Horn_p_a (AnnFormula f) = is_Horn_p_a (strip_anno f)
is_Horn_p_a _ = False

is_Ghorn_f :: Formula -> Bool
is_Ghorn_f (Quantified q _ f _) = (is_Atomic_q q) && (is_Ghorn_f f)
is_Ghorn_f (Connect AndOp l _) = (is_Ghorn_c_conj l) || (is_Ghorn_f_conj l)
is_Ghorn_f (Connect ImplOp [f,g] _) = (is_Ghorn_prem f) && (is_Ghorn_conc g)
is_Ghorn_f (Connect IfOp [g,f] _) = (is_Ghorn_prem f) && (is_Ghorn_conc g)
is_Ghorn_f (Connect EquivOp [f,g] _) = (is_Ghorn_prem f) && (is_Ghorn_prem g)
is_Ghorn_f (TrueAtom _) = True
is_Ghorn_f (PredAppl _ _ _ _ _) = True
is_Ghorn_f (TermTest _ _ _) = True
is_Ghorn_f (ElemTest _ _ _) = True
is_Ghorn_f (AnnFormula f) = is_Ghorn_f (strip_anno f)
is_Ghorn_f _ = False

is_Ghorn_c_conj :: [Formula] -> Bool
is_Ghorn_c_conj l = and ((map is_Ghorn_conc) l)

is_Ghorn_f_conj :: [Formula] -> Bool
is_Ghorn_f_conj l = and ((map is_Ghorn_f) l)

is_Ghorn_p_conj :: [Formula] -> Bool
is_Ghorn_p_conj l = and ((map is_Ghorn_prem) l)

is_Ghorn_prem :: Formula -> Bool
is_Ghorn_prem (Connect AndOp l _) = is_Ghorn_p_conj l
is_Ghorn_prem x = is_Horn_p_a x

is_Ghorn_conc :: Formula -> Bool
is_Ghorn_conc (Connect AndOp l _) = is_Ghorn_c_conj l
is_Ghorn_conc x = is_Horn_a x

get_Logic :: Formula -> CASL_Sublogics
get_Logic f = if (is_Atomic_f f) then bottom else
              if (is_Horn_f f) then need_horn else
              if (is_Ghorn_f f) then need_ghorn else
              need_fol

-- for the formula inside a subsort-defn
get_Logic_sd :: Formula -> CASL_Sublogics
get_Logic_sd f = if (is_Horn_p_a f) then need_horn else
                 if (is_Ghorn_prem f) then need_ghorn else
                 need_fol

------------------------------------------------------------------------------
-- functions to compute minimal sublogic for a given element
------------------------------------------------------------------------------

sl_basic_spec :: BASIC_SPEC -> CASL_Sublogics
sl_basic_spec (Basic_spec l) = comp_list $ map sl_basic_items
                                         $ map strip_anno l

sl_basic_items :: BASIC_ITEMS -> CASL_Sublogics
sl_basic_items (Sig_items i) = sl_sig_items i
sl_basic_items (Free_datatype l _) = comp_list $ map sl_datatype_decl
                                               $ map strip_anno l
sl_basic_items (Sort_gen l _) = sublogics_max need_cons
                                (comp_list $ map sl_sig_items
                                           $ map strip_anno l)
sl_basic_items (Var_items l _) = comp_list $ map sl_var_decl l
sl_basic_items (Local_var_axioms d l _) = sublogics_max
                                          (comp_list $ map sl_var_decl d)
                                          (comp_list $ map sl_formula
                                                     $ map strip_anno l)
sl_basic_items (Axiom_items l _) = comp_list $ map sl_formula
                                             $ map strip_anno l

sl_sig_items :: SIG_ITEMS -> CASL_Sublogics
sl_sig_items (Sort_items l _) = comp_list $ map sl_sort_item $ map strip_anno l
sl_sig_items (Op_items l _) = comp_list $ map sl_op_item $ map strip_anno l
sl_sig_items (Pred_items l _) = comp_list $ map sl_pred_item $ map strip_anno l
sl_sig_items (Datatype_items l _) = comp_list $ map sl_datatype_decl
                                              $ map strip_anno l

sl_sort_item :: SORT_ITEM -> CASL_Sublogics
sl_sort_item (Subsort_decl _ _ _) = need_sub
sl_sort_item (Subsort_defn _ _ _ f _) = sublogics_max
                                        (get_logic_sd $ strip_anno f)
                                        (sublogics_max need_sub
                                        (sl_formula $ strip_anno f))
sl_sort_item _ = bottom

sl_op_item :: OP_ITEM -> CASL_Sublogics
sl_op_item (Op_decl _ t l _) = sublogics_max (sl_op_type t)
                               (comp_list $ map sl_op_attr l)
sl_op_item (Op_defn _ h t _) = sublogics_max (sl_op_head h)
                                             (sl_term $ strip_anno t)

sl_op_attr :: OP_ATTR -> CASL_Sublogics
sl_op_attr (Unit_op_attr t) = sl_term t
sl_op_attr _ = bottom

sl_op_type :: OP_TYPE -> CASL_Sublogics
sl_op_type (Partial_op_type _ _ _) = need_part
sl_op_type _ = bottom

sl_op_head :: OP_HEAD -> CASL_Sublogics
sl_op_head (Partial_op_head _ _ _) = need_part
sl_op_head _ = bottom

sl_pred_item :: PRED_ITEM -> CASL_Sublogics
sl_pred_item (Pred_decl _ _ _) = need_pred
sl_pred_item (Pred_defn _ _ f _) = sublogics_max need_pred
                                                 (sl_formula $ strip_anno f)

sl_datatype_decl :: DATATYPE_DECL -> CASL_Sublogics
sl_datatype_decl (Datatype_decl _ l _) = comp_list $ map sl_alternative
                                                   $ map strip_anno l

sl_alternative :: ALTERNATIVE -> CASL_Sublogics
sl_alternative (Total_construct _ l _) =  comp_list $ map sl_components l
sl_alternative (Partial_construct _ l _) = comp_list $ map sl_components l
sl_alternative (Subsorts _ _) = need_sub

sl_components :: COMPONENTS -> CASL_Sublogics
sl_components (Partial_select _ _ _) = need_part
sl_components _ = bottom

sl_var_decl :: VAR_DECL -> CASL_Sublogics
sl_var_decl _ = bottom

sl_term :: TERM -> CASL_Sublogics
sl_term (Cast _ _ _) = need_part
sl_term (Conditional t f u _) = sublogics_max (sl_term t)
                                (sublogics_max (sl_formula f) (sl_term u))
sl_term _ = bottom

sl_formula :: FORMULA -> CASL_Sublogics
sl_formula f = sublogics_max (get_logic f) (sl_form f)

sl_form :: FORMULA -> CASL_Sublogics
sl_form (Quantification _ _ f _) = sl_form f
sl_form (Conjunction l _) = comp_list $ map sl_form l
sl_form (Disjunction l _) = comp_list $ map sl_form l
sl_form (Implication f g _) = sublogics_max (sl_form f) (sl_form g)
sl_form (Equivalence f g _) = sublogics_max (sl_form f) (sl_form g)
sl_form (Negation f _) = sl_form f
sl_form (True_atom _) = bottom
sl_form (False_atom _) = bottom
sl_form (Predication _ l _) = sublogics_max need_pred
                              (comp_list $ map sl_term l)
sl_form (Definedness t _) = sl_term t
sl_form (Existl_equation t u _) = sublogics_max need_eq
                                  (sublogics_max (sl_term t) (sl_term u))
sl_form (Strong_equation t u _) = sublogics_max need_eq
                                  (sublogics_max (sl_term t) (sl_term u))
sl_form (Membership t _ _) = sublogics_max need_sub (sl_term t)
sl_form (Mixfix_formula t) = sl_term t
sl_form (Unparsed_formula _ _) = bottom

sl_sentence :: Sentence -> CASL_Sublogics
sl_sentence (Axiom a) = sl_axiom $ strip_anno a
sl_sentence (GenItems i _) = sl_genitems i

sl_axiom :: Axiom -> CASL_Sublogics
sl_axiom (AxiomDecl _ f _) = sl_Formula f

sl_genitems :: GenItems -> CASL_Sublogics
sl_genitems l = comp_list $ map sl_symbol l

sl_symb_items :: SYMB_ITEMS -> CASL_Sublogics
sl_symb_items (Symb_items k l _) = sublogics_max (sl_symb_kind k)
                                   (comp_list $ map sl_symb l)

sl_symb_items_list :: SYMB_ITEMS_LIST -> CASL_Sublogics
sl_symb_items_list (Symb_items_list l _) = comp_list $ map sl_symb_items l

sl_symb_kind :: SYMB_KIND -> CASL_Sublogics
sl_symb_kind (Preds_kind) = need_pred
sl_symb_kind _ = bottom

sl_symb :: SYMB -> CASL_Sublogics
sl_symb (Symb_id _) = bottom
sl_symb (Qual_id _ t _) = sl_type t

sl_type :: TYPE -> CASL_Sublogics
sl_type (O_type t) = sl_op_type t
sl_type (P_type _) = need_pred

sl_symb_map_items :: SYMB_MAP_ITEMS -> CASL_Sublogics
sl_symb_map_items (Symb_map_items k l _) = sublogics_max (sl_symb_kind k)
                                          (comp_list $ map sl_symb_or_map l)

sl_symb_map_items_list :: SYMB_MAP_ITEMS_LIST -> CASL_Sublogics
sl_symb_map_items_list (Symb_map_items_list l _) = 
    comp_list $ map sl_symb_map_items l

sl_symb_or_map :: SYMB_OR_MAP -> CASL_Sublogics
sl_symb_or_map (Symb s) = sl_symb s
sl_symb_or_map (Symb_map s t _) = sublogics_max (sl_symb s) (sl_symb t)

sl_sign :: Sign -> CASL_Sublogics
sl_sign (SignAsList l) = comp_list $ map sl_sigitem l

sl_sigitem :: SigItem -> CASL_Sublogics
sl_sigitem (ASortItem i) = sl_sortitem $ strip_anno i
sl_sigitem (AnOpItem i) = sl_opitem $ strip_anno i
sl_sigitem (APredItem i) = sl_preditem $ strip_anno i

sl_sortitem :: SortItem -> CASL_Sublogics
sl_sortitem (SortItem _ r d _ _) = sublogics_max (sl_sortrels r)
                                                 (mb sl_sortdefn d)

sl_sortdefn :: SortDefn -> CASL_Sublogics
sl_sortdefn (SubsortDefn _ f _) = sublogics_max (sl_Formula f)
                                                (get_Logic_sd f)

sl_sortrels :: SortRels -> CASL_Sublogics
sl_sortrels (SortRels [] [] [] []) = bottom
sl_sortrels _ = need_sub

sl_opitem :: OpItem -> CASL_Sublogics
sl_opitem (OpItem _ t l d _ _) = sublogics_max (sl_optype t)
                                 (sublogics_max (mb sl_opdefn d)
                                 (comp_list $ map sl_opattr l))

sl_opattr :: OpAttr -> CASL_Sublogics
sl_opattr (UnitOpAttr t) = sl_Term t
sl_opattr _ = bottom

sl_optype :: OpType -> CASL_Sublogics
sl_optype (OpType k _ _) = sl_funkind k

sl_funkind :: FunKind -> CASL_Sublogics
sl_funkind (Partial) = need_part
sl_funkind _ = bottom

sl_opdefn :: OpDefn -> CASL_Sublogics
sl_opdefn (OpDef _ t _) = sl_Term (strip_anno t)
sl_opdefn (Constr c) = sl_symbol c
sl_opdefn (Select l s) = sublogics_max (sl_symbol s)
                                       (comp_list $ map sl_symbol l)

sl_preditem :: PredItem -> CASL_Sublogics
sl_preditem (PredItem _ _ d _ _) = mb sl_preddefn d

sl_preddefn :: PredDefn -> CASL_Sublogics
sl_preddefn (PredDef _ f _) = sl_Formula f

sl_Term :: Term -> CASL_Sublogics
sl_Term (OpAppl _ t l _ _) = sublogics_max (sl_optype t)
                                           (comp_list $ map sl_Term l)
sl_Term (Typed t _ _ _) = sl_Term t
sl_Term (Cond t f u _) = sublogics_max (sl_Term t)
                         (sublogics_max (sl_Formula f) (sl_Term u))
sl_Term _ = bottom

sl_Formula :: Formula -> CASL_Sublogics
sl_Formula f = sublogics_max (get_Logic f) (sl_Form f)

sl_Form :: Formula -> CASL_Sublogics
sl_Form (Quantified _ _ f _) = sl_Form f
sl_Form (Connect _ l _) = comp_list $ map sl_Form l
sl_Form (TermTest _ l _) = comp_list $ map sl_Term l
sl_Form (PredAppl _ _ l _ _) = sublogics_max need_pred
                                             (comp_list $ map sl_Term l)
sl_Form (ElemTest t _ _) = sublogics_max need_sub (sl_Term t)
sl_Form (FalseAtom _) = bottom
sl_Form (TrueAtom _) = bottom
sl_Form (AnnFormula f) = sl_Form $ strip_anno f

sl_morphism :: Morphism -> CASL_Sublogics
sl_morphism (Morphism a b _ f p) = sublogics_max
                                   (sublogics_max (sl_sign a) (sl_sign b))
                                   (sublogics_max (sl_fun_map f)
                                                  (sl_pred_map p))

sl_fun_map_entry :: (OpType, Id, Bool) -> CASL_Sublogics
sl_fun_map_entry (t,_,_) = sl_optype t

sl_fun_map_entries :: [(OpType, Id, Bool)] -> CASL_Sublogics
sl_fun_map_entries l = comp_list $ map sl_fun_map_entry l

sl_fun_map :: Fun_map -> CASL_Sublogics
sl_fun_map fm = comp_list $ map sl_fun_map_entries $ map snd $ fmToList fm

sl_pred_map :: Pred_map -> CASL_Sublogics
sl_pred_map fm = if (isEmptyFM fm) then bottom else need_pred

sl_symbol :: Symbol -> CASL_Sublogics
sl_symbol (Symbol _ t) = sl_symbtype t

sl_symbtype :: SymbType -> CASL_Sublogics
sl_symbtype (OpAsItemType t) = sl_optype t
sl_symbtype (PredType _) = need_pred
sl_symbtype _ = bottom

sl_Alternative :: Alternative -> CASL_Sublogics
sl_Alternative (Construct i t c _) =
  sublogics_max (sl_optype t) (comp_list $ map sl_Component c)
sl_Alternative (Subsort _ _) = need_sub

sl_Component :: Component -> CASL_Sublogics
sl_Component (Component _ t _) = sl_optype t

------------------------------------------------------------------------------
-- comparison functions
------------------------------------------------------------------------------

nimpl :: Bool -> Bool -> Bool
nimpl True _      = True
nimpl False False = True
nimpl False True  = False

sl_in :: CASL_Sublogics -> CASL_Sublogics -> Bool
sl_in given new = (nimpl (has_sub given) (has_sub new)) &&
                  (nimpl (has_part given) (has_part new)) &&
                  (nimpl (has_cons given) (has_cons new)) &&
                  (nimpl (has_eq given) (has_eq new)) &&
                  (nimpl (has_pred given) (has_pred new)) &&
                  ((which_logic given) >= (which_logic new))

in_x :: CASL_Sublogics -> a -> (a -> CASL_Sublogics) -> Bool
in_x l x f = sl_in l (f x)

in_basic_spec :: CASL_Sublogics -> BASIC_SPEC -> Bool
in_basic_spec l x = in_x l x sl_basic_spec

in_sentence :: CASL_Sublogics -> Sentence -> Bool
in_sentence l x = in_x l x sl_sentence

in_symb_items :: CASL_Sublogics -> SYMB_ITEMS -> Bool
in_symb_items l x = in_x l x sl_symb_items

in_symb_map_items :: CASL_Sublogics -> SYMB_MAP_ITEMS -> Bool
in_symb_map_items l x = in_x l x sl_symb_map_items

in_symb_items_list :: CASL_Sublogics -> SYMB_ITEMS_LIST -> Bool
in_symb_items_list l x = in_x l x sl_symb_items_list

in_symb_map_items_list :: CASL_Sublogics -> SYMB_MAP_ITEMS_LIST -> Bool
in_symb_map_items_list l x = in_x l x sl_symb_map_items_list

in_sign :: CASL_Sublogics -> Sign -> Bool
in_sign l x = in_x l x sl_sign

in_morphism :: CASL_Sublogics -> Morphism -> Bool
in_morphism l x = in_x l x sl_morphism

in_symbol :: CASL_Sublogics -> Symbol -> Bool
in_symbol l x = in_x l x sl_symbol

------------------------------------------------------------------------------
-- projection functions
------------------------------------------------------------------------------

pr_annoted :: CASL_Sublogics -> (CASL_Sublogics -> a -> Maybe a) -> Annoted a -> Maybe (Annoted a)
pr_annoted sl f (Annoted e p l r) =
           let
             res = f sl e
           in
             if (isNothing res) then Nothing else
             Just (Annoted (fromJust res) p l r)

pr_check :: CASL_Sublogics -> (a -> CASL_Sublogics) -> a -> Maybe a
pr_check l f e = if (in_x l e f) then (Just e) else Nothing

pr_formula :: CASL_Sublogics -> FORMULA -> Maybe FORMULA
pr_formula l f = pr_check l sl_formula f

pr_basic_spec :: CASL_Sublogics -> BASIC_SPEC -> BASIC_SPEC
pr_basic_spec l (Basic_spec s) =
              Basic_spec ((mapMaybe (pr_annoted l pr_basic_items)) s)

pr_basic_items :: CASL_Sublogics -> BASIC_ITEMS -> Maybe BASIC_ITEMS
pr_basic_items l (Sig_items s) =
               let
                 res = pr_sig_items l s
               in
                 if (isNothing res) then Nothing else
                 Just (Sig_items (fromJust res))
pr_basic_items l (Free_datatype d p) =
               let
                 (res,pos) = mapPos (tln 2 p)
                                    (pr_annoted l pr_datatype_decl) d
               in
                 if (res==[]) then Nothing else
                 Just (Free_datatype res ((topn 2 p) ++ pos))
pr_basic_items l (Sort_gen s p) =
               if (has_cons l) then
                 let
                   res = mapMaybe (pr_annoted l pr_sig_items) s
                 in
                   if (res==[]) then Nothing else
                   Just (Sort_gen res p)
               else
                 Nothing
pr_basic_items l (Var_items v p) = Just (Var_items v p)
pr_basic_items l (Local_var_axioms v f p) =
               let
                 (res,pos) = mapPos (tln (length v) p)
                                    (pr_annoted l pr_formula) f
               in
                 if (res==[]) then Nothing else
                 Just (Local_var_axioms v res ((topn (length v) p) ++ pos))
pr_basic_items l (Axiom_items f p) =
               let
                 (res,pos) = mapPos p (pr_annoted l pr_formula) f
               in
                 if (res==[]) then Nothing else
                 Just (Axiom_items res pos)

pr_datatype_decl :: CASL_Sublogics -> DATATYPE_DECL -> Maybe DATATYPE_DECL
pr_datatype_decl l d = pr_check l sl_datatype_decl d

pr_symbol :: CASL_Sublogics -> Symbol -> Maybe Symbol
pr_symbol l s = pr_check l sl_symbol s

pr_sig_items :: CASL_Sublogics -> SIG_ITEMS -> Maybe SIG_ITEMS
pr_sig_items l (Sort_items s p) =
             let
               (res,pos) = mapPos (tln 1 p)
                                  (pr_annoted l pr_sort_item) s
             in
               if (res==[]) then Nothing else
               Just (Sort_items res ((topn 1 p) ++ pos))
pr_sig_items l (Op_items o p) =
             let
               (res,pos) = mapPos (tln 1 p)
                                  (pr_annoted l pr_op_item) o
             in
               if (res==[]) then Nothing else
               Just (Op_items res ((topn 1 p) ++ pos))
pr_sig_items l (Pred_items i p) =
             if (has_pred l) then
               Just (Pred_items i p)
             else
               Nothing
pr_sig_items l (Datatype_items d p) =
             let
               (res,pos) = mapPos (tln 1 p)
                                  (pr_annoted l pr_datatype_decl) d
             in
               if (res==[]) then Nothing else
               Just (Datatype_items res ((topn 1 p) ++ pos))

pr_op_item :: CASL_Sublogics -> OP_ITEM -> Maybe OP_ITEM
pr_op_item l i = pr_check l sl_op_item i

pr_sort_item :: CASL_Sublogics -> SORT_ITEM -> Maybe SORT_ITEM
pr_sort_item l (Sort_decl s p) = Just (Sort_decl s p)
pr_sort_item l (Subsort_decl sl s p) =
             if (has_sub l) then
               Just (Subsort_decl sl s p)
             else
               Just (Sort_decl (s:sl) [])
pr_sort_item l (Subsort_defn s1 v s2 f p) =
             if (has_sub l) then
               Just (Subsort_defn s1 v s2 f p)
             else
               Just (Sort_decl [s1] [])
pr_sort_item l (Iso_decl s p) = Just (Iso_decl s p)

pr_symb_items :: CASL_Sublogics -> SYMB_ITEMS -> Maybe SYMB_ITEMS
pr_symb_items l (Symb_items k s p) =
              if (in_x l k sl_symb_kind) then
                let
                  (res,pos) = mapPos (tln 1 p) (pr_symb l) s
                in
                  if (res==[]) then Nothing else
                  Just (Symb_items k res ((topn 1 p) ++ pos))
              else
                Nothing

pr_symb_map_items :: CASL_Sublogics -> SYMB_MAP_ITEMS -> Maybe SYMB_MAP_ITEMS
pr_symb_map_items l (Symb_map_items k s p) =
                  if (in_x l k sl_symb_kind) then
                    let
                      (res,pos) = mapPos (tln 1 p) (pr_symb_or_map l) s
                    in
                      if (res==[]) then Nothing else
                      Just (Symb_map_items k res ((topn 1 p) ++ pos))
                  else
                    Nothing

pr_symb_or_map :: CASL_Sublogics -> SYMB_OR_MAP -> Maybe SYMB_OR_MAP
pr_symb_or_map l (Symb s) =
               let
                 res = pr_symb l s
               in
                 if (isNothing res) then Nothing else
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
pr_symb l (Symb_id i) = Just (Symb_id i)
pr_symb l (Qual_id i t p) =
        if (in_x l t sl_type) then
          Just (Qual_id i t p)
        else
          Nothing

pr_sign :: CASL_Sublogics -> Sign -> Sign
pr_sign l (SignAsList s) = SignAsList (mapMaybe (pr_sigitem l) s)

pr_sigitem :: CASL_Sublogics -> SigItem -> Maybe SigItem
pr_sigitem l (ASortItem s) =
  Just (ASortItem (fromJust (pr_annoted l pr_sortitem s)))
pr_sigitem l (AnOpItem o)  =
  let
    res = pr_annoted l pr_opitem o
  in
    if (isJust res) then Just (AnOpItem (fromJust res))
    else Nothing
pr_sigitem l (APredItem p) =
  let
    res = pr_annoted l pr_preditem p
  in
    if (isJust res) then Just (APredItem (fromJust res))
    else Nothing

pr_sortitem :: CASL_Sublogics -> SortItem -> Maybe SortItem
pr_sortitem l (SortItem id rels def pos alt) =
  if (has_sub l) then
    Just (SortItem id rels (pr_sortdefn l def) pos alt)
  else
    Just (SortItem id (SortRels [] [] [] []) (pr_sortdefn l def) pos alt)

pr_sortdefn :: CASL_Sublogics -> Maybe SortDefn -> Maybe SortDefn
pr_sortdefn l Nothing = Nothing
pr_sortdefn l (Just (SubsortDefn v f p)) =
  if (has_sub l) then
    let
      res = pr_Formula l f
    in
      if (isJust res) then Just (SubsortDefn v (fromJust res) p)
      else Nothing
  else
    Nothing
pr_sortdefn l (Just (Datatype alt kind items p)) =
  let
    a = mapMaybe (pr_annoted l pr_Alternative) alt
    b = pr_genitems l items
  in
    if (isJust b) then
    Just (Datatype a kind (fromJust b) p)
    else Nothing

pr_genitems :: CASL_Sublogics -> GenItems -> Maybe GenItems
pr_genitems l i = let
                    res = mapMaybe (pr_symbol l) i
                  in
                    if (res==[]) then Nothing else
                    Just res

pr_Alternative :: CASL_Sublogics -> Alternative -> Maybe Alternative
pr_Alternative l a = pr_check l sl_Alternative a

pr_Formula :: CASL_Sublogics -> Formula -> Maybe Formula
pr_Formula l f = pr_check l sl_Formula f

pr_opitem :: CASL_Sublogics -> OpItem -> Maybe OpItem
pr_opitem l i = pr_check l sl_opitem i

pr_preditem :: CASL_Sublogics -> PredItem -> Maybe PredItem
pr_preditem l i = pr_check l sl_preditem i

pr_morphism :: CASL_Sublogics -> Morphism -> Morphism
pr_morphism l (Morphism s t sm fm pm) =
  Morphism (pr_sign l s) (pr_sign l t) sm (pr_fun_map l fm) (pr_pred_map l pm)

pr_pred_map :: CASL_Sublogics -> Pred_map -> Pred_map
pr_pred_map l x = if (has_pred l) then x else emptyFM

add_to_fm :: [(Id,[(OpType,Id,Bool)])] -> Fun_map -> Fun_map
add_to_fm [] fm = fm
add_to_fm ((a,b):t) fm = add_to_fm t (addToFM fm a b)

pr_fun_map :: CASL_Sublogics -> Fun_map -> Fun_map
pr_fun_map l m = add_to_fm (map (pr_fun_map_entries l) $ fmToList m) emptyFM

pr_fun_map_entries :: CASL_Sublogics -> (Id,[(OpType,Id,Bool)]) -> (Id,[(OpType,Id,Bool)])
pr_fun_map_entries l (i,ll) = (i,mapMaybe (pr_fun_map_entry l) ll)

pr_fun_map_entry :: CASL_Sublogics -> (OpType,Id,Bool) -> Maybe (OpType,Id,Bool)
pr_fun_map_entry l (t,i,b) =
  if (has_part l) then
    Just (t,i,b)
  else
    let
      res = pr_check l sl_optype t
    in
      if ((isJust res) && (not b)) then
      Just (t,i,b) else Nothing

pr_epsilon :: CASL_Sublogics -> Sign -> Morphism
pr_epsilon l s = (Morphism (pr_sign l s) s emptyFM emptyFM emptyFM)
  -- Einbettungs-Signaturmorphismus, ueber Funktion in LocalEnv.hs

------------------------------------------------------------------------------
-- the end
------------------------------------------------------------------------------

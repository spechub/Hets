{- HetCATS/CASL/Sublogics.hs
   $Id$
   Authors: Pascal Schmidt
   Year:    2002

   todo:

   sublogic_names :: id -> sublogics -> [String] 
             -- the first name is the principal name
         all_sublogics :: id -> [sublogics]
  <=
  meet, join :: l -> l -> l  -- meet = "Durschnitt"
  top :: l

Weitere Instanzen mit HasCASL, CASL-LTL etc.
  (nur sich selbst als Sublogic)
Logic-Representations (Sublogic immer = top)

Alles zusammenfassen in LogicGraph.hs

min_sublogic_basic_spec  Analysefunktion: für basic spec Bitmaske berechnen
   (Bits fuer Features setzen und rekursiv verodern)
is_in_basic_spec  Testfunktion: pruefen, ob errechnete Bitmaske <= vorgegebene

-}

module Sublogics_CASL where

import AS_Annotation
import AS_Basic_CASL
import LocalEnv

------------------------------------------------------------------------------
-- datatypes for CASL sublogics
------------------------------------------------------------------------------

data CASL_Formulas = FOL     -- first-order logic
                   | GHorn   -- generalized positive conditional logic
                   | Horn    -- positive conditional logic
                   | Atomic  -- atomic logic
                   deriving (Show,Ord,Eq)

data CASL_Sublogics = CASL_SL
                      { has_sub::Bool,   -- subsorting
                        has_part::Bool,  -- partiality
                        has_cons::Bool,  -- sort generation contraints
                        has_eq::Bool,    -- equality
                        has_pred::Bool,  -- predicates
                        which_logic::CASL_Formulas
                      } deriving (Show,Eq)

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

sublogics_name :: CASL_Sublogics -> String
sublogics_name x = ( if (has_sub x) then "Sub" else "" ) ++
                   ( if (has_part x) then "P" else "") ++
                   ( if (has_cons x) then "C" else "") ++
                   ( formulas_name (has_pred x) (which_logic x) ) ++
                   ( if (has_eq x) then "=" else "")

------------------------------------------------------------------------------
-- min and max functions
------------------------------------------------------------------------------

formulas_max :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_max FOL _    = FOL
formulas_max _ FOL    = FOL
formulas_max GHorn _  = GHorn
formulas_max _ GHorn  = GHorn
formulas_max Horn _   = Horn
formulas_max _ Horn   = Horn
formulas_max _ _ = Atomic

formulas_min :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_min Atomic _ = Atomic
formulas_min _ Atomic = Atomic
formulas_min Horn _   = Horn
formulas_min _ Horn   = Horn
formulas_min GHorn _  = GHorn
formulas_min _ GHorn  = GHorn
formulas_min _ _      = FOL

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

and_list :: [Bool] -> Bool
and_list []    = True
and_list (h:t) = h && (and_list t)

mb :: (a -> CASL_Sublogics) -> Maybe a -> CASL_Sublogics
mb f Nothing = bottom
mb f (Just x) = f x

------------------------------------------------------------------------------
-- functions to analyse formulae
------------------------------------------------------------------------------

is_atomic_f :: FORMULA -> Bool
is_atomic_f (Quantification q _ f _) = (is_atomic_q q) && (is_atomic_f f)
is_atomic_f (Conjunction l _) = and_list ((map is_atomic_f) l)
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
is_horn_p_conj (Conjunction l _) = and_list ((map is_horn_p_a) l)
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
is_ghorn_c_conj l = and_list ((map is_ghorn_conc) l)

is_ghorn_f_conj :: [FORMULA] -> Bool
is_ghorn_f_conj l = and_list ((map is_ghorn_f) l)

is_ghorn_p_conj :: [FORMULA] -> Bool
is_ghorn_p_conj l = and_list ((map is_ghorn_prem) l)

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

------------------------------------------------------------------------------
-- functions to compute minimal sublogic for a given element
------------------------------------------------------------------------------

sl_basic_spec :: BASIC_SPEC -> CASL_Sublogics
sl_basic_spec (Basic_spec l) = comp_list ((map sl_basic_items)
                                          ((map strip_anno) l))

sl_basic_items :: BASIC_ITEMS -> CASL_Sublogics
sl_basic_items (Sig_items i) = sl_sig_items i
sl_basic_items (Free_datatype l _) = comp_list ((map sl_datatype_decl)
                                                ((map strip_anno) l))
sl_basic_items (Sort_gen l _) = sublogics_max need_cons
                                (comp_list ((map sl_sig_items)
                                            ((map strip_anno) l)))
sl_basic_items (Var_items l _) = comp_list ((map sl_var_decl) l)
sl_basic_items (Local_var_axioms d l _) = sublogics_max
                                          (comp_list ((map sl_var_decl) d))
                                          (comp_list ((map sl_formula)
                                                      ((map strip_anno) l)))
sl_basic_items (Axiom_items l _) = comp_list ((map sl_formula)
                                              ((map strip_anno) l))

sl_sig_items :: SIG_ITEMS -> CASL_Sublogics
sl_sig_items (Sort_items l _) = comp_list ((map sl_sort_item)
                                           ((map strip_anno) l))
sl_sig_items (Op_items l _) = comp_list ((map sl_op_item)
                                         ((map strip_anno) l))
sl_sig_items (Pred_items l _) = comp_list ((map sl_pred_item)
                                           ((map strip_anno) l))
sl_sig_items (Datatype_items l _) = comp_list ((map sl_datatype_decl)
                                               ((map strip_anno) l))

sl_sort_item :: SORT_ITEM -> CASL_Sublogics
sl_sort_item (Subsort_decl _ _ _) = need_sub
sl_sort_item (Subsort_defn _ _ _ f _) = sublogics_max need_sub
                                        (sl_formula (strip_anno f))
sl_sort_item _ = bottom

sl_op_item :: OP_ITEM -> CASL_Sublogics
sl_op_item (Op_decl _ t l _) = sublogics_max (sl_op_type t)
                               (comp_list ((map sl_op_attr) l))
sl_op_item (Op_defn _ h t _) = sublogics_max (sl_op_head h)
                                             (sl_term (strip_anno t))

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
                                                 (sl_formula (strip_anno f))

sl_datatype_decl :: DATATYPE_DECL -> CASL_Sublogics
sl_datatype_decl (Datatype_decl _ l _) = comp_list ((map sl_alternative)
                                                    ((map strip_anno) l))

sl_alternative :: ALTERNATIVE -> CASL_Sublogics
sl_alternative (Total_construct _ l _) =  comp_list ((map sl_components) l)
sl_alternative (Partial_construct _ l _) = comp_list ((map sl_components) l)
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
sl_formula _ = top

sl_quantifier :: QUANTIFIER -> CASL_Sublogics
sl_quantifier (Existential) = need_fol
sl_quantifier (Unique_existential) = need_fol
sl_quantifier _ = bottom

sl_sentence :: Sentence -> CASL_Sublogics
sl_sentence (Axiom a) = sl_axiom (strip_anno a)
sl_sentence (GenItems i _) = sl_genitems i

sl_axiom :: Axiom -> CASL_Sublogics
sl_axiom (AxiomDecl _ f _) = sl_Formula f

sl_genitems :: GenItems -> CASL_Sublogics
sl_genitems l = comp_list ((map sl_symbol) l)

sl_symb_items :: SYMB_ITEMS -> CASL_Sublogics
sl_symb_items _ = top

sl_symb_map_items :: SYMB_MAP_ITEMS -> CASL_Sublogics
sl_symb_map_items _ = top

sl_sign :: Sign -> CASL_Sublogics
sl_sign (SignAsList l) = comp_list ((map sl_sigitem) l)

sl_sigitem :: SigItem -> CASL_Sublogics
sl_sigitem (ASortItem i) = sl_sortitem (strip_anno i)
sl_sigitem (AnOpItem i) = sl_opitem (strip_anno i)
sl_sigitem (APredItem i) = sl_preditem (strip_anno i)

sl_sortitem :: SortItem -> CASL_Sublogics
sl_sortitem (SortItem _ r d _ _) = sublogics_max (sl_sortrels r)
                                                 (mb sl_sortdefn d)

sl_sortdefn :: SortDefn -> CASL_Sublogics
sl_sortdefn (SubsortDefn _ f _) = sl_Formula f

sl_sortrels :: SortRels -> CASL_Sublogics
sl_sortrels (SortRels [] [] [] []) = bottom
sl_sortrels _ = need_sub

sl_opitem :: OpItem -> CASL_Sublogics
sl_opitem (OpItem _ t l d _ _) = sublogics_max (sl_optype t)
                                 (sublogics_max (mb sl_opdefn d)
                                 (comp_list ((map sl_opattr) l)))

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
                                       (comp_list ((map sl_symbol) l))

sl_preditem :: PredItem -> CASL_Sublogics
sl_preditem (PredItem _ _ d _ _) = mb sl_preddefn d

sl_preddefn :: PredDefn -> CASL_Sublogics
sl_preddefn (PredDef _ f _) = sl_Formula f

sl_Term :: Term -> CASL_Sublogics
sl_Term (OpAppl _ t l _ _) = sublogics_max (sl_optype t)
                                           (comp_list ((map sl_Term) l))
sl_Term (Typed t _ _ _) = sl_Term t
sl_Term (Cond t f u _) = sublogics_max (sl_Term t)
                         (sublogics_max (sl_Formula f) (sl_Term u))
sl_Term _ = bottom

sl_Formula :: Formula -> CASL_Sublogics
sl_Formula _ = top

-- sl_morphism :: Morphism -> CASL_Sublogics
-- sl_morphism _ = top

sl_symbol :: Symbol -> CASL_Sublogics
sl_symbol (Symbol _ t) = sl_symbtype t

sl_symbtype :: SymbType -> CASL_Sublogics
sl_symbtype (OpAsItemType t) = sl_optype t
sl_symbtype (PredType _) = need_pred
sl_symbtype _ = bottom

------------------------------------------------------------------------------
-- the end
------------------------------------------------------------------------------

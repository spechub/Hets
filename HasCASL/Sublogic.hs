{- |
Module      :  $Header$
Copyright   :  (c) Pascal Schmidt, Christian Maeder, and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs) for
  HasCASL. The functions allow to compute the minimal sublogics needed by a
  given element, to check whether an item is part of a given sublogic, and --
  not yet -- to project an element into a given sublogic.
-}

module HasCASL.Sublogic ( -- * datatypes
                   HasCASL_Sublogics(..),
                   HasCASL_Formulas(..),

                   -- * functions for LatticeWithTop instance
                   top,
                   sublogics_max,
                   sublogics_min,

                   -- * functions for Logic instance

                   -- * sublogic to string converstion
                   sublogics_name,

                   -- * list of all sublogics
                   sublogics_all,

                   -- * checks if element is in given sublogic
                   in_basicSpec,
                   in_sentence,
                   in_symbItems,
                   in_symbMapItems,
                   in_env,
                   in_morphism,
                   in_symbol,

                   -- * computes the sublogic of a given element
                   sl_basicSpec,
                   sl_sentence,
                   sl_symbItems,
                   sl_symbMapItems,
                   sl_env,
                   sl_morphism,
                   sl_symbol,

                 ) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import Common.Id

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin

------------------------------------------------------------------------------
-- | Datatypes for HasCASL sublogics
------------------------------------------------------------------------------

data HasCASL_Formulas = Atomic  -- atomic logic
                   | Horn    -- positive conditional logic
                   | GHorn   -- generalized positive conditional logic
                   | FOL     -- first-order logic
                   | HOL     -- higher-order logic
                   deriving (Show,Ord,Eq)

data HasCASL_Sublogics = HasCASL_SL
                      { has_sub :: Bool,   -- subsorting
                        has_part :: Bool,  -- partiality
                        has_eq :: Bool,    -- equality
                        has_pred :: Bool,  -- predicates
                        has_ho :: Bool,  -- higher order
                        has_type_classes :: Bool,
                        has_polymorphism :: Bool,
                        has_type_constructors :: Bool,
                        which_logic::HasCASL_Formulas
                      } deriving (Show,Ord,Eq)


-----------------------------------------------------------------------------
-- Special sublogics elements
-----------------------------------------------------------------------------

-- top element
--
top :: HasCASL_Sublogics
top = (HasCASL_SL True True True True True True True True HOL)

-- bottom element
--
bottom :: HasCASL_Sublogics
bottom = (HasCASL_SL False False False False False False False False Atomic)

-- the following are used to add a needed feature to a given
-- sublogic via sublogics_max, i.e. (sublogics_max given needs_part)
-- will force partiality in addition to what features given already
-- has included

-- minimal sublogic with subsorting
--
need_sub :: HasCASL_Sublogics
need_sub = bottom { has_sub = True }

-- minimal sublogic with partiality
--
need_part :: HasCASL_Sublogics
need_part = bottom { has_part = True }

-- minimal sublogic with equality
--
need_eq :: HasCASL_Sublogics
need_eq = bottom { has_eq = True }

-- minimal sublogic with predicates
--
need_pred :: HasCASL_Sublogics
need_pred = bottom { has_pred = True }

-- minimal sublogic with higher order
--
need_ho :: HasCASL_Sublogics
need_ho = bottom { has_ho = True }

-- minimal sublogic with type classes
--
need_type_classes :: HasCASL_Sublogics
need_type_classes = bottom { has_type_classes = True }

-- minimal sublogic with polymorhism
--
need_polymorphism :: HasCASL_Sublogics
need_polymorphism = bottom { has_polymorphism = True }

-- minimal sublogic with type constructors
--
need_type_constructors :: HasCASL_Sublogics
need_type_constructors = bottom { has_type_constructors = True }

need_horn :: HasCASL_Sublogics
need_horn = bottom { which_logic = Horn }

need_ghorn :: HasCASL_Sublogics
need_ghorn = bottom { which_logic = GHorn }

need_fol :: HasCASL_Sublogics
need_fol = bottom { which_logic = FOL }

need_hol :: HasCASL_Sublogics
need_hol = bottom { which_logic = HOL }

-----------------------------------------------------------------------------
-- Functions to generate a list of all sublogics for HasCASL
-----------------------------------------------------------------------------

sublogics_all :: [HasCASL_Sublogics]
sublogics_all = [HasCASL_SL {has_sub = sub,
                             has_part = part,
                             has_eq = eq,
                             has_pred = pre,
                             has_ho = ho,
                             has_type_classes = tyCl,
                             has_polymorphism = poly,
                             has_type_constructors = tyCon,
                             which_logic = logic}
                  | sub <- [False,True],
                    part <- [False,True],
                    eq <- [False,True],
                    pre <- [False,True],
                    ho <- [False,True],
                    tyCl <- [False,True],
                    poly <- [False,True],
                    tyCon <- [False,True],
                    logic <- [Atomic, Horn, GHorn, FOL, HOL] ]

------------------------------------------------------------------------------
-- Conversion functions (to String)
------------------------------------------------------------------------------

-- "formulas_name :: has_pred -> has_ho -> which_logic -> String"
formulas_name :: Bool -> Bool -> HasCASL_Formulas -> String
formulas_name True  True  HOL    = "HOL"
formulas_name True  False HOL    = "HOL"  -- ?!
formulas_name False True  HOL    = "HOL"
formulas_name False False HOL    = "HOL"  -- ?!
formulas_name True  True  FOL    = "HOL"  -- ?!
formulas_name True  False FOL    = "FOL"
formulas_name False True  FOL    = "HO-FOAlg"  -- ?!
formulas_name False False FOL    = "FOAlg"
formulas_name True  True  GHorn  = "HO-GHorn"
formulas_name True  False GHorn  = "GHorn"
formulas_name False True  GHorn  = "HO-GCond"
formulas_name False False GHorn  = "GCond"
formulas_name True  True  Horn   = "HO-Horn"
formulas_name True  False Horn   = "Horn"
formulas_name False True  Horn   = "HO-Cond"
formulas_name False False Horn   = "Cond"
formulas_name True  True  Atomic = "HO-Atom"
formulas_name True  False Atomic = "Atom"
formulas_name False True  Atomic = "HO-Eq"
formulas_name False False Atomic = "Eq"

sublogics_name :: HasCASL_Sublogics -> [String]
sublogics_name x = [
     ( if (has_sub  x) then "Sub" else "")
  ++ ( if (has_part x) then "P"   else "")
  ++ ( if (has_type_classes x) then "TyCl"   else "")
  ++ ( if (has_polymorphism x) then "Poly"   else "")
  ++ ( if (has_type_constructors x) then "TyCons"   else "")
  ++ ( formulas_name (has_pred x) (has_ho x) (which_logic x) )
  ++ ( if (has_eq   x) then "="   else "")]

------------------------------------------------------------------------------
-- min/join and max/meet functions
------------------------------------------------------------------------------

formulas_max :: HasCASL_Formulas -> HasCASL_Formulas -> HasCASL_Formulas
formulas_max x y = if (x<y) then y else x

formulas_min :: HasCASL_Formulas -> HasCASL_Formulas -> HasCASL_Formulas
formulas_min x y = if (x<y) then x else y

sublogics_max :: HasCASL_Sublogics -> HasCASL_Sublogics -> HasCASL_Sublogics
sublogics_max a b = HasCASL_SL
                      (has_sub a               || has_sub  b)
                      (has_part a              || has_part b)
                      (has_eq a                || has_eq b)
                      (has_pred a              || has_pred b)
                      (has_ho a                || has_ho b)
                      (has_type_classes a      || has_type_classes b)
                      (has_polymorphism a      || has_polymorphism b)
                      (has_type_constructors a || has_type_constructors b)
                      (formulas_max (which_logic a) (which_logic b))

sublogics_min :: HasCASL_Sublogics -> HasCASL_Sublogics -> HasCASL_Sublogics
sublogics_min a b = HasCASL_SL
                      (has_sub a               && has_sub  b)
                      (has_part a              && has_part b)
                      (has_eq a                && has_eq   b)
                      (has_pred a              && has_pred b)
                      (has_ho a                && has_ho b)
                      (has_type_classes a      && has_type_classes b)
                      (has_polymorphism a      && has_polymorphism b)
                      (has_type_constructors a && has_type_constructors b)
                      (formulas_min (which_logic a) (which_logic b))

------------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------------

-- compute sublogics from a list of sublogics
--
comp_list :: [HasCASL_Sublogics] -> HasCASL_Sublogics
comp_list l = foldl sublogics_max bottom l

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

   They are adapted for HasCASL, especially HasCASLs abstract syntax (As.hs)
--------------------------------------------------------------------------- -}

-- Atomic Logic (subsection 3.4 of the paper)

-- FORMULA, P-ATOM
--
is_atomic_t :: Term -> Bool
is_atomic_t (QuantifiedTerm q _ t _) = (is_atomic_q q) && (is_atomic_t t)
is_atomic_t (ApplTerm (QualOp Fun (InstOpId i _ _) t _) (TupleTerm ts _) _) =
 -- P-Conjunction and ExEq
      (((i == andId)
         && (and $ map is_atomic_t ts))
       || (i == exEq))
   && (t == logType)
   && (not (null ts))
is_atomic_t (QualOp Fun  (InstOpId i _ _) t _) =
     (i == trueId)
  && (t == logType)
--is_atomic_t (Predication _ _ _) = True
is_atomic_t (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) _ _) =
     (i == defId)
  && (t == logType)
is_atomic_t _ = False

-- QUANTIFIER
--
is_atomic_q :: Quantifier -> Bool
is_atomic_q (Universal) = True
is_atomic_q _           = False

-- Positive Conditional Logic (subsection 3.2 in the paper)

-- FORMULA
--
is_horn_t :: Term -> Bool
is_horn_t (QuantifiedTerm q _ f _) =
     (is_atomic_q q)
  && (is_horn_t f)
is_horn_t (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm f _) _) =
     (i == implId)
  && (t == logType)
  && (is_horn_p_conj (head f))
  && (is_horn_a (last f))
is_horn_t _ = False

-- P-CONJUNCTION
--
is_horn_p_conj :: Term -> Bool
is_horn_p_conj (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm ts _) _) =
      (i == andId)
   && (t == logType)
   && (not (null ts))
   && (and $ map is_horn_a ts)
is_horn_p_conj _ = False

-- ATOM
--
is_horn_a :: Term -> Bool
is_horn_a (QualOp Fun  (InstOpId i _ _) t _) =
     (i == trueId)
  && (t == logType)
-- is_horn_a (Predication _ _ _) = True
is_horn_a (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) _ _) =
     ((i == defId)
       || (i == exEq)
       || (i == eqId))
  && (t == logType)
--is_horn_a (Membership _ _ _) = True
is_horn_a _ = False

-- P-ATOM
--
is_horn_p_a :: Term -> Bool
is_horn_p_a (QualOp Fun  (InstOpId i _ _) t _) =
     (i == trueId)
  && (t == logType)
-- is_horn_p_a (Predication _ _ _) = True
is_horn_p_a (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) _ _) =
     ((i == defId)
       || (i == exEq))
  && (t == logType)
-- is_horn_p_a (Membership _ _ _) = True
is_horn_p_a _ = False

-- Generalized Positive Conditional Logic (subsection 3.3 of the paper)

-- FORMULA, ATOM
--
is_ghorn_t :: Term -> Bool
is_ghorn_t (QuantifiedTerm q _ t _) = (is_atomic_q q) && (is_ghorn_t t)
is_ghorn_t (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm f _) _) =
     (t == logType)
  && (((i == andId) && (not (null f)) &&  ((is_ghorn_c_conj f) || (is_ghorn_f_conj f)))
      ||
      ((i == implId) && (is_ghorn_prem (head f)) && (is_ghorn_conc (last f)))
      ||
      ((i == eqvId) && (is_ghorn_prem (head f)) && (is_ghorn_prem (last f))))
is_ghorn_t (QualOp Fun  (InstOpId i _ _) t _) =
     (i == trueId)
  && (t == logType)
-- is_ghorn_t (Predication _ _ _) = True
is_ghorn_t (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) _ _) =
     ((i == defId)
       || (i == exEq)
       || (i == eqId))
  && (t == logType)
-- is_ghorn_t (Membership _ _ _) = True
is_ghorn_t _ = False

-- C-CONJUNCTION
--
is_ghorn_c_conj :: [Term] -> Bool
is_ghorn_c_conj t = (not(null t)) && (and ((map is_ghorn_conc) t))

-- F-CONJUNCTION
--
is_ghorn_f_conj :: [Term] -> Bool
is_ghorn_f_conj t = (not(null t)) && (and ((map is_ghorn_t) t))

-- P-CONJUNCTION
--
is_ghorn_p_conj :: [Term] -> Bool
is_ghorn_p_conj t = (not(null t)) && (and (map is_ghorn_prem t))

-- PREMISE
--
is_ghorn_prem :: Term -> Bool
is_ghorn_prem (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm ts _) _) =
     (i == andId)
  && (t == logType)
  && (not (null ts))
  && (is_ghorn_p_conj ts)
is_ghorn_prem x = is_horn_p_a x

-- CONCLUSION
--
is_ghorn_conc :: Term -> Bool
is_ghorn_conc (ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm ts _) _) =
     (i == andId)
  && (t == logType)
  && (not (null ts))
  && (is_ghorn_c_conj ts)
is_ghorn_conc x = is_horn_a x

is_fol_t :: Term -> Bool
is_fol_t (LambdaTerm _ _ _ _) = False
is_fol_t (CaseTerm _ _ _) = False
is_fol_t (LetTerm _ _ _ _) = False
is_fol_t _ = True
{- FOL:
  no lambda/let/case,
  no higher types (i.e. all types are basic, tuples, or tuple -> basic)
-}
-- compute logic of a formula by checking all logics in turn
--
get_logic :: Term -> HasCASL_Sublogics
get_logic t = if (is_atomic_t t) then bottom else
                if (is_horn_t t) then need_horn else
                  if (is_ghorn_t t) then need_ghorn else
                    if (is_fol_t t) then need_fol else
                      need_hol


------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element; these work
-- by recursing into all subelements
------------------------------------------------------------------------------

sl_basicSpec :: BasicSpec -> HasCASL_Sublogics
sl_basicSpec (BasicSpec l) = comp_list $ map sl_basicItem
                                       $ map item l


sl_basicItem :: BasicItem -> HasCASL_Sublogics
sl_basicItem (SigItems l) = sl_sigItems l
sl_basicItem (ProgItems l _) = comp_list $ map sl_progEq
                                         $ map item l
sl_basicItem (ClassItems _ l _) = sublogics_max need_type_classes
                                    (comp_list $ map sl_classItem
                                               $ map item l)
sl_basicItem (GenVarItems l _) = comp_list $ map sl_genVarDecl l
sl_basicItem (FreeDatatype l _) = comp_list $ map sl_datatypeDecl
                                            $ map item l
sl_basicItem (GenItems l _) = (comp_list $ map sl_sigItems
                                         $ map item l)
sl_basicItem (AxiomItems l m _) = sublogics_max
                                     (comp_list $ map sl_genVarDecl l)
                                     (comp_list $ map sl_term
                                                $ map item m)
sl_basicItem (Internal l _) = comp_list $ map sl_basicItem
                                        $ map item l


sl_sigItems :: SigItems -> HasCASL_Sublogics
sl_sigItems (TypeItems i l _) = sublogics_max (sl_instance i)
                                  (comp_list $ map sl_typeItem
                                             $ map item l)
sl_sigItems (OpItems b l _) = sublogics_max (sl_opBrand b)
                                (comp_list $ map sl_opItem
                                           $ map item l)


sl_opBrand :: OpBrand -> HasCASL_Sublogics
sl_opBrand (Pred) = need_pred
sl_opBrand _ = bottom


sl_instance :: Instance -> HasCASL_Sublogics
sl_instance (Instance) = need_type_classes
sl_instance _ = bottom


sl_classItem :: ClassItem -> HasCASL_Sublogics
sl_classItem (ClassItem c l _) = sublogics_max (sl_classDecl c)
                                   (comp_list $ map sl_basicItem
                                              $ map item l)


sl_classDecl :: ClassDecl -> HasCASL_Sublogics
sl_classDecl (ClassDecl _ _ _) = need_type_classes

sl_Rawkind :: RawKind -> HasCASL_Sublogics
sl_Rawkind (ClassKind _) = bottom
sl_Rawkind (FunKind _ _ _ _) = need_hol

sl_kind :: Kind -> HasCASL_Sublogics
sl_kind (ClassKind i) = if i == universeId then bottom else need_type_classes
sl_kind (FunKind _ k1 k2 _) = comp_list [need_hol, (sl_kind k1), (sl_kind k2)]

sl_typeItem :: TypeItem -> HasCASL_Sublogics
sl_typeItem (TypeDecl l k _) = sublogics_max (sl_kind k)
                                 (comp_list $ map sl_typePattern l)
sl_typeItem (SubtypeDecl l _ _) = sublogics_max need_sub
                                    (comp_list $ map sl_typePattern l)
sl_typeItem (IsoDecl l _) = sublogics_max need_sub
                              (comp_list $ map sl_typePattern l)
sl_typeItem (SubtypeDefn tp _ t term _) =
  comp_list [need_sub,
             (sl_typePattern tp),
             (sl_type t),
             (sl_term (item term))]
sl_typeItem (AliasType tp (Just k) ts _) = comp_list [(sl_kind k), (sl_typePattern tp),
                                             (sl_typeScheme ts)]
sl_typeItem (AliasType tp Nothing ts _) = sublogics_max (sl_typePattern tp)
                                                        (sl_typeScheme ts)
sl_typeItem (Datatype dDecl) = sl_datatypeDecl dDecl


sl_typePattern :: TypePattern -> HasCASL_Sublogics
sl_typePattern (TypePattern _ l _) = comp_list $ map sl_typeArg l
-- non-empty args --> type constructor!
sl_typePattern (MixfixTypePattern l) = comp_list $ map sl_typePattern l
sl_typePattern (BracketTypePattern _ l _) = comp_list $ map sl_typePattern l
sl_typePattern (TypePatternArg _ _) = need_polymorphism
sl_typePattern _ = bottom

sl_type :: Type -> HasCASL_Sublogics
sl_type = sl_BasicFun

sl_Basictype :: Type -> HasCASL_Sublogics
sl_Basictype ty = case ty of
    TypeName _ k v -> sublogics_max
        (if v /= 0 then need_polymorphism else bottom) $ sl_Rawkind k
    KindedType t k _ -> sublogics_max (sl_Basictype t) $ sl_kind k
    ExpandedType _ t -> sl_Basictype t
    BracketType Parens [t] _ -> sl_Basictype t
    _ -> case getTypeAppl ty of
         (TypeName ide _ _, [_, _]) | isArrow ide ->
            sublogics_max need_ho $ sl_BasicFun ty
         (TypeName ide _ _, [arg]) | ide == lazyTypeId ->
            sublogics_max need_hol $ sl_Basictype arg
         (_, args) -> comp_list $ need_type_constructors :
                      map sl_Basictype args

sl_BasicProd :: Type -> HasCASL_Sublogics
sl_BasicProd ty = case getTypeAppl ty of
    (TypeName ide _ _, tyArgs@(_:_:_)) | ide == productId (length tyArgs)
        -> comp_list $ map sl_Basictype tyArgs
    _ -> sl_Basictype ty

sl_BasicFun :: Type -> HasCASL_Sublogics
sl_BasicFun ty = case getTypeAppl ty of
    (TypeName ide _ _, [arg, res]) | isArrow ide ->
           comp_list [if isPartialArrow ide then need_part else bottom,
              sl_BasicProd arg, sl_Basictype res]
    _ -> sl_Basictype ty

-- FOL i.e. no higher types (i.e. all types are basic, tuples, or tuple -> basic)
sl_typeScheme :: TypeScheme -> HasCASL_Sublogics
sl_typeScheme (TypeScheme l t _) =
  comp_list $ sl_type t : map sl_typeArg l

sl_opItem :: OpItem -> HasCASL_Sublogics
sl_opItem (OpDecl l t m _) =
  comp_list [(comp_list $ map sl_opId l),
             (sl_typeScheme t),
             (comp_list $ map sl_opAttr m)]
sl_opItem (OpDefn i v ts p t _) =
  comp_list [(sl_opId i),
             (comp_list $ map sl_varDecl (concat v)),
             (sl_typeScheme ts),
             (sl_partiality p),
             (sl_term t)]


sl_partiality :: Partiality -> HasCASL_Sublogics
sl_partiality (Partial) = need_part
sl_partiality _ = bottom


sl_opAttr :: OpAttr -> HasCASL_Sublogics
sl_opAttr (UnitOpAttr t _) = sl_term t
sl_opAttr _ = need_eq


sl_datatypeDecl :: DatatypeDecl -> HasCASL_Sublogics
sl_datatypeDecl (DatatypeDecl t k l c _) =
  let sl = comp_list [(sl_typePattern t),
                      (sl_kind k),
                      (comp_list $ map sl_alternative
                                 $ map item l)]
  in
    if (null c) then sl
      else sublogics_max need_type_classes sl


sl_alternative :: Alternative -> HasCASL_Sublogics
sl_alternative (Constructor _ l p _) =  sublogics_max (sl_partiality p)
                                          (comp_list $ map sl_component
                                                            (concat l))
sl_alternative (Subtype l _) = sublogics_max need_sub
                                 (comp_list $ map sl_type l)


sl_component :: Component -> HasCASL_Sublogics
sl_component (Selector _ p t _ _) =
   sublogics_max (sl_partiality p) (sl_type t)
sl_component (NoSelector t) = sl_type t


sl_term :: Term -> HasCASL_Sublogics
sl_term t = sublogics_max (get_logic t) (sl_t t)


sl_t :: Term -> HasCASL_Sublogics
sl_t (QualVar vd) = sl_varDecl vd
sl_t (QualOp b i t _) =
  comp_list [(sl_opBrand b),
             (sl_instOpId i),
             (sl_typeScheme t)]
--sl_t (ResolvedMixTerm _ l _) = comp_list $ map sl_t l
sl_t (ApplTerm t1 t2 _) = sublogics_max (sl_t t1) (sl_t t2)
sl_t (TupleTerm l _) = comp_list $ map sl_t l
sl_t (TypedTerm t _ ty _) = sublogics_max (sl_t t) (sl_type ty)
sl_t (QuantifiedTerm _ l t _) = sublogics_max (sl_t t)
                                 (comp_list $ map sl_genVarDecl l)
sl_t (LambdaTerm l p t _) =
  comp_list [(comp_list $ map sl_pattern l),
             (sl_partiality p),
             (sl_t t)]
sl_t (CaseTerm t l _) = sublogics_max (sl_t t)
                          (comp_list $ map sl_progEq l)
sl_t (LetTerm _ l t _) = sublogics_max (sl_t t)
                           (comp_list $ map sl_progEq l)
sl_t (MixTypeTerm _ t _) = sl_type t
sl_t (MixfixTerm l) = comp_list $ map sl_t l
sl_t (BracketTerm _ l _) = comp_list $ map sl_t l
sl_t (AsPattern vd p2 _) = sublogics_max (sl_varDecl vd) (sl_pattern p2)
sl_t _ = bottom


sl_pattern :: Pattern -> HasCASL_Sublogics
sl_pattern = sl_t


sl_progEq :: ProgEq -> HasCASL_Sublogics
sl_progEq (ProgEq p t _) = sublogics_max (sl_pattern p) (sl_t t)


sl_varDecl :: VarDecl -> HasCASL_Sublogics
sl_varDecl (VarDecl _ t _ _) = sl_type t

sl_varKind :: VarKind -> HasCASL_Sublogics
sl_varKind vk = case vk of
   VarKind k -> sl_kind k
   Downset t -> sublogics_max need_sub $ sl_type t
   _ -> bottom

sl_typeArg :: TypeArg -> HasCASL_Sublogics
sl_typeArg (TypeArg _ _ k _ _ _ _) =
    sublogics_max need_polymorphism (sl_varKind k)


sl_genVarDecl :: GenVarDecl -> HasCASL_Sublogics
sl_genVarDecl (GenVarDecl v) = sl_varDecl v
sl_genVarDecl (GenTypeVarDecl v) = sl_typeArg v


sl_opId :: OpId -> HasCASL_Sublogics
sl_opId (OpId _ l _) = comp_list $ map sl_typeArg l

sl_instOpId :: InstOpId -> HasCASL_Sublogics
sl_instOpId (InstOpId i l _) =
  if ((i == exEq) || (i == eqId))
    then sublogics_max need_eq (comp_list $ map sl_type l)
      else comp_list $ map sl_type l


sl_symbItems :: SymbItems -> HasCASL_Sublogics
sl_symbItems (SymbItems k l _ _) = sublogics_max (sl_symbKind k)
                                     (comp_list $ map sl_symb l)


sl_symbMapItems :: SymbMapItems -> HasCASL_Sublogics
sl_symbMapItems (SymbMapItems k l _ _) = sublogics_max (sl_symbKind k)
                                           (comp_list $ map sl_symbOrMap l)


sl_symbKind :: SymbKind -> HasCASL_Sublogics
sl_symbKind (SK_pred) = need_pred
sl_symbKind (SK_class) = need_type_classes
sl_symbKind _ = bottom


sl_symb :: Symb -> HasCASL_Sublogics
sl_symb (Symb _ Nothing _) = bottom
sl_symb (Symb _ (Just l) _) = sl_symbType l


sl_symbType :: SymbType -> HasCASL_Sublogics
sl_symbType (SymbType t) = sl_typeScheme t


sl_symbOrMap :: SymbOrMap -> HasCASL_Sublogics
sl_symbOrMap (SymbOrMap s Nothing _) = sl_symb s
sl_symbOrMap (SymbOrMap s (Just t) _) =
  sublogics_max (sl_symb s) (sl_symb t)


-- the maps have no influence since all sorts,ops,preds in them
-- must also appear in the signatures, so any features needed by
-- them will be included by just checking the signatures
--

sl_env :: Env -> HasCASL_Sublogics
sl_env e =
    let classes = if Map.null $ classMap e
                    then bottom else need_type_classes
        types = comp_list $ map sl_typeInfo (Map.elems (typeMap e))
        ops = comp_list $ map sl_opInfos (Map.elems (assumps e))
        in comp_list [classes, types, ops]

sl_typeInfo :: TypeInfo -> HasCASL_Sublogics
sl_typeInfo t = let s = sl_typeDefn (typeDefn t) in
                    if Set.null $ superTypes t then s else
                    sublogics_max need_sub  s

sl_typeDefn :: TypeDefn -> HasCASL_Sublogics
sl_typeDefn (DatatypeDefn de) = sl_dataEntry de
sl_typeDefn (AliasTypeDefn t) = sl_typeScheme t
sl_typeDefn _ = bottom


sl_dataEntry :: DataEntry -> HasCASL_Sublogics
sl_dataEntry (DataEntry _ _ _ l _ m) =
  sublogics_max (comp_list $ map sl_typeArg l)
                (comp_list $ map sl_altDefn m)


sl_opInfos :: OpInfos -> HasCASL_Sublogics
sl_opInfos o = comp_list $ map sl_opInfo (opInfos o)


sl_opInfo :: OpInfo -> HasCASL_Sublogics
sl_opInfo o = comp_list [(sl_typeScheme (opType o)),
                         (comp_list $ map sl_opAttr (opAttrs o)),
                         (sl_opDefn (opDefn o))]


sl_opDefn :: OpDefn -> HasCASL_Sublogics
sl_opDefn (NoOpDefn b) = sl_opBrand b
sl_opDefn (SelectData l _) = comp_list $ map sl_constrInfo l
sl_opDefn (Definition b t) =
  sublogics_max (sl_opBrand b) (sl_term t)
sl_opDefn _ = bottom


sl_constrInfo :: ConstrInfo -> HasCASL_Sublogics
sl_constrInfo c = sl_typeScheme (constrType c)


sl_sentence :: Sentence -> HasCASL_Sublogics
sl_sentence (Formula t) = sl_term t
sl_sentence (ProgEqSen _ ts pq) =
  sublogics_max (sl_typeScheme ts) (sl_progEq pq)
sl_sentence (DatatypeSen l) = comp_list $ map sl_dataEntry l


sl_altDefn :: AltDefn -> HasCASL_Sublogics
sl_altDefn (Construct _ l p m) =
  comp_list [(comp_list $ map sl_type l),
             (sl_partiality p),
             (comp_list $ map sl_selector $ concat m)]

sl_selector :: Selector -> HasCASL_Sublogics
sl_selector (Select _ t p) = sublogics_max (sl_type t)
                                           (sl_partiality p)


sl_morphism :: Morphism -> HasCASL_Sublogics
sl_morphism m = sublogics_max (sl_env $ msource m) (sl_env $ mtarget m)


sl_symbol :: Symbol -> HasCASL_Sublogics
sl_symbol (Symbol _ t e) =
  sublogics_max (sl_symbolType t) (sl_env e)


sl_symbolType :: SymbolType a -> HasCASL_Sublogics
sl_symbolType (OpAsItemType t) = sl_typeScheme t
sl_symbolType (ClassAsItemType _) = need_type_classes
sl_symbolType _ = bottom


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
sl_in :: HasCASL_Sublogics -> HasCASL_Sublogics -> Bool
sl_in given new = (nimpl (has_sub  given) (has_sub  new)) &&
                  (nimpl (has_part given) (has_part new)) &&
                  (nimpl (has_eq   given) (has_eq   new)) &&
                  (nimpl (has_pred given) (has_pred new)) &&
                  (nimpl (has_polymorphism given)
                                  (has_polymorphism new)) &&
                  (nimpl (has_ho   given) (has_ho   new)) &&
                  (nimpl (has_type_classes given)
                                  (has_type_classes new)) &&
                  (nimpl (has_type_constructors given)
                             (has_type_constructors new)) &&
                  ((which_logic given) >= (which_logic new))

in_x :: HasCASL_Sublogics -> a -> (a -> HasCASL_Sublogics) -> Bool
in_x l x f = sl_in l (f x)

in_basicSpec :: HasCASL_Sublogics -> BasicSpec -> Bool
in_basicSpec l x = in_x l x sl_basicSpec

in_sentence :: HasCASL_Sublogics -> Sentence -> Bool
in_sentence l x = in_x l x sl_sentence

in_symbItems :: HasCASL_Sublogics -> SymbItems -> Bool
in_symbItems l x = in_x l x sl_symbItems

in_symbMapItems :: HasCASL_Sublogics -> SymbMapItems -> Bool
in_symbMapItems l x = in_x l x sl_symbMapItems

in_env :: HasCASL_Sublogics -> Env -> Bool
in_env l x = in_x l x sl_env

in_morphism :: HasCASL_Sublogics -> Morphism -> Bool
in_morphism l x = in_x l x sl_morphism

in_symbol :: HasCASL_Sublogics -> Symbol -> Bool
in_symbol l x = in_x l x sl_symbol

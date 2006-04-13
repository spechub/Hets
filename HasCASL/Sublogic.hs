{- |
Module      :  $Header$
Copyright   :  (c) Sonja Groening, C. Maeder, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs) for
  HasCASL. The functions allow to compute the minimal sublogic needed by a
  given element, to check whether an item is part of a given sublogic, and --
  not yet -- to project an element into a given sublogic.
-}
{- todo: test computations
-}

module HasCASL.Sublogic
    ( -- * datatypes
    , Sublogic(..)
    , Formulas(..)
    , Classes(..)
      -- * functions for LatticeWithTop instance
    , topLogic
    , sublogic_max
    , sublogic_min
      -- * further sublogic constants
    , bottom
    , noSubtypes
    , noClasses
    , totalFuns
    , caslLogic
      -- * functions for Logic instance
      -- ** sublogic to string converstion
    , sublogic_name
      -- ** list of all sublogics
    , sublogics_all
      -- ** checks if element is in given sublogic
    , in_basicSpec
    , in_sentence
    , in_symbItems
    , in_symbMapItems
    , in_env
    , in_morphism
    , in_symbol
      -- * computes the sublogic of a given element
    , sl_basicSpec
    , sl_sentence
    , sl_symbItems
    , sl_symbMapItems
    , sl_env
    , sl_morphism
    , sl_symbol
    ) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import Common.Id

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.FoldTerm

-- | formula kinds of HasCASL sublogics
data Formulas
    = Atomic  -- ^ atomic logic
    | Horn    -- ^ positive conditional logic
    | GHorn   -- ^ generalized positive conditional logic
    | FOL     -- ^ first-order logic
    | HOL     -- ^ higher-order logic
      deriving (Show, Eq, Ord)

data Classes = NoClasses | SimpleTypeClasses | ConstructorClasses
               deriving (Show, Eq, Ord)

-- | HasCASL sublogics
data Sublogic = Sublogic
    { has_sub :: Bool   -- ^ subsorting
    , has_part :: Bool  -- ^ partiality
    , has_eq :: Bool    -- ^ equality
    , has_pred :: Bool  -- ^ predicates
    , has_ho :: Bool    -- ^ higher order
    , type_classes :: Classes
    , has_polymorphism :: Bool
    , has_type_constructors :: Bool
    , which_logic :: Formulas
    } deriving (Show, Eq, Ord)

-- * special sublogic elements

-- | top element
topLogic :: Sublogic
topLogic = Sublogic
    { has_sub = True
    , has_part = True
    , has_eq = True
    , has_pred = True
    , has_ho = True
    , type_classes = ConstructorClasses
    , has_polymorphism = True
    , has_type_constructors = True
    , which_logic = HOL
    }

-- | top sublogic without subtypes
noSubtypes :: Sublogic
noSubtypes = topLogic { has_sub = False }

-- | top sublogic without type classes
noClasses :: Sublogic
noClasses = topLogic { type_classes = NoClasses }

-- | top sublogic without partiality
totalFuns :: Sublogic
totalFuns = topLogic { has_part = False }

caslLogic :: Sublogic
caslLogic = noClasses
    { has_ho = False
    , has_polymorphism = False
    , has_type_constructors = False
    , which_logic = FOL
    }

-- | bottom sublogic
bottom :: Sublogic
bottom = Sublogic
    { has_sub = False
    , has_part = False
    , has_eq = False
    , has_pred = False
    , has_ho = False
    , type_classes = NoClasses
    , has_polymorphism = False
    , has_type_constructors = False
    , which_logic = Atomic
    }

-- the following are used to add a needed feature to a given
-- sublogic via sublogic_max, i.e. (sublogic_max given needs_part)
-- will force partiality in addition to what features given already
-- has included

-- | minimal sublogic with subsorting
need_sub :: Sublogic
need_sub = bottom { has_sub = True }

-- | minimal sublogic with partiality
need_part :: Sublogic
need_part = bottom { has_part = True }

-- | minimal sublogic with equality
need_eq :: Sublogic
need_eq = bottom { has_eq = True }

-- | minimal sublogic with predicates
need_pred :: Sublogic
need_pred = bottom { has_pred = True }

-- | minimal sublogic with higher order
need_ho :: Sublogic
need_ho = bottom { has_ho = True }

-- | minimal sublogic with simple type classes
simpleTypeClasses :: Sublogic
simpleTypeClasses = bottom { type_classes = SimpleTypeClasses }

-- | minimal sublogic with constructor classes
constructorClasses :: Sublogic
constructorClasses = bottom { type_classes = ConstructorClasses }

-- | minimal sublogic with polymorhism
need_polymorphism :: Sublogic
need_polymorphism = bottom { has_polymorphism = True }

-- | minimal sublogic with type constructors
need_type_constructors :: Sublogic
need_type_constructors = bottom { has_type_constructors = True }

need_horn :: Sublogic
need_horn = bottom { which_logic = Horn }

need_ghorn :: Sublogic
need_ghorn = bottom { which_logic = GHorn }

need_fol :: Sublogic
need_fol = bottom { which_logic = FOL }

need_hol :: Sublogic
need_hol = bottom { which_logic = HOL }

-- | generate a list of all sublogics for HasCASL
sublogics_all :: [Sublogic]
sublogics_all = let bools = [False,True] in
    [ Sublogic
    { has_sub = sub
    , has_part = part
    , has_eq = eq
    , has_pred = pre
    , has_ho = ho
    , type_classes = tyCl
    , has_polymorphism = poly
    , has_type_constructors = tyCon
    , which_logic = logic
    }
    | sub <- bools
    , part <- bools
    , eq <- bools
    , pre <- bools
    , ho <- bools
    , tyCl <- [NoClasses, SimpleTypeClasses, ConstructorClasses]
    , poly <- bools
    , tyCon <- bools
    , logic <- [Atomic, Horn, GHorn, FOL, HOL]
    ]

-- | conversion functions to String
formulas_name :: Bool -> Bool -> Formulas -> String
formulas_name hasPred hasHo f =
    let addHo = if hasHo then ("HO-" ++) else id in case f of
    HOL -> "HOL"
    FOL -> if hasPred then if hasHo then "HOL" else "FOL"
           else addHo "FOAlg"
    _ -> addHo $ case f of
         Atomic -> if hasPred then "Atom" else "Eq"
         _ -> (case f of
                GHorn -> ("G" ++)
                _ -> id) $ if hasPred then "Horn" else "Cond"

-- | the sublogic name as a singleton string list
sublogic_name :: Sublogic -> [String]
sublogic_name x = [
     (if has_sub x then "Sub" else "")
  ++ (if has_part x then "P" else "")
  ++ (case type_classes x of
         NoClasses -> ""
         SimpleTypeClasses -> "TyCl"
         ConstructorClasses -> "CoCl")
  ++ (if has_polymorphism x then "Poly" else "")
  ++ (if has_type_constructors x && not (has_polymorphism x)
       then "TyCons" else "")
  ++ formulas_name (has_pred x) (has_ho x) (which_logic x)
  ++ (if has_eq x then "=" else "")]

-- * join functions
sublogic_join :: (Bool -> Bool -> Bool)
               -> (Classes -> Classes -> Classes)
               -> (Formulas -> Formulas -> Formulas)
               -> Sublogic -> Sublogic -> Sublogic
sublogic_join joinB joinC joinF a b = Sublogic
    { has_sub = joinB (has_sub a) $ has_sub b
    , has_part = joinB (has_part a) $ has_part b
    , has_eq = joinB (has_eq a) $ has_eq b
    , has_pred = joinB (has_pred a) $ has_pred b
    , has_ho = joinB (has_ho a) $ has_ho b
    , type_classes = joinC (type_classes a) $ type_classes b
    , has_polymorphism = joinB (has_polymorphism a) $ has_polymorphism b
    , has_type_constructors =
        joinB (has_type_constructors a) $ has_type_constructors b
    , which_logic = joinF (which_logic a) $ which_logic b
    }

sublogic_max :: Sublogic -> Sublogic -> Sublogic
sublogic_max = sublogic_join max max max

sublogic_min :: Sublogic -> Sublogic -> Sublogic
sublogic_min = sublogic_join min min min

-- | compute union sublogic from a list of sublogics
comp_list :: [Sublogic] -> Sublogic
comp_list l = foldl sublogic_max bottom l

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

isPredication :: Term -> Bool
isPredication = foldTerm FoldRec
    { foldQualVar = \ _ _ -> True
    , foldQualOp = \ _ b (InstOpId i _ _) t _ ->
                   b /= Fun && not (elem (i, t) bList)
    , foldApplTerm = \ _ b1 b2 _ -> b1 && b2
    , foldTupleTerm = \ _ bs _ -> and bs
    , foldTypedTerm = \ _ b q _ _ -> q /= InType && b
    , foldAsPattern = \ _ _ _ _ -> False
    , foldQuantifiedTerm = \ _ _ _ _ _ -> False
    , foldLambdaTerm = \ _ _ _ _ _ -> False
    , foldCaseTerm = \ _ _ _ _ -> False
    , foldLetTerm = \ _ _ _ _ _ -> False
    , foldResolvedMixTerm = \ _ i bs _ ->
          not (elem i $ map fst bList) && and bs
    , foldTermToken = \ _ _ -> True
    , foldMixTypeTerm = \ _ q _ _ -> q /= InType
    , foldMixfixTerm = \ _ bs -> and bs
    , foldBracketTerm = \ _ _ bs _ -> and bs
    , foldProgEq = \ _ _ _ _ -> False
    }

-- FORMULA, P-ATOM
is_atomic_t :: Term -> Bool
is_atomic_t term = case term of
    QuantifiedTerm q _ t _ | is_atomic_q q && is_atomic_t t -> True
      -- P-Conjunction and ExEq
    ApplTerm (QualOp Fun (InstOpId i _ _) t _) arg _
      | (case arg of
        TupleTerm ts@[_, _] _ ->
            i == andId && t == logType && and (map is_atomic_t ts)
            || i == exEq && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    QualOp Fun (InstOpId i _ _) t _
        | i == trueId && t == unitTypeScheme -> True
    _ -> isPredication term

-- QUANTIFIER
is_atomic_q :: Quantifier -> Bool
is_atomic_q q = case q of
    Universal -> True
    _ -> False

-- Positive Conditional Logic (subsection 3.2 in the paper)

-- FORMULA
is_horn_t :: Term -> Bool
is_horn_t term = case term of
    QuantifiedTerm q _ f _ -> is_atomic_q q && is_horn_t f
    ApplTerm (QualOp Fun (InstOpId i _ _) t _) (TupleTerm [t1, t2] _) _
        | i == implId && t == logType && is_horn_p_conj t1 && is_horn_a t2
          -> True
    _ -> is_atomic_t term

-- P-CONJUNCTION
is_horn_p_conj :: Term -> Bool
is_horn_p_conj term = case term of
    ApplTerm (QualOp Fun (InstOpId i _ _) t _) (TupleTerm ts@[_, _] _) _
        | i == andId && t == logType && and (map is_horn_a ts)
          -> True
    _ -> is_atomic_t term

-- ATOM
is_horn_a :: Term -> Bool
is_horn_a term = case term of
    QualOp Fun  (InstOpId i _ _) t _
        | i == trueId && t == unitTypeScheme -> True
    ApplTerm (QualOp Fun (InstOpId i _ _) t _) arg _
      | (case arg of
        TupleTerm [_, _] _ -> (i == exEq || i == eqId) && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    --is_horn_a (Membership _ _ _) = True
    _ -> is_atomic_t term

-- P-ATOM
is_horn_p_a :: Term -> Bool
is_horn_p_a term = case term of
    QualOp Fun (InstOpId i _ _) t _
        | i == trueId && t == unitTypeScheme -> True
    ApplTerm (QualOp Fun  (InstOpId i _ _) t _) arg _
      | (case arg of
        TupleTerm [_, _] _ -> i == exEq && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    -- is_horn_p_a (Membership _ _ _) = True
    _ -> is_atomic_t term

-- Generalized Positive Conditional Logic (subsection 3.3 of the paper)

-- FORMULA, ATOM
is_ghorn_t :: Term -> Bool
is_ghorn_t term = case term of
    QuantifiedTerm q _ t _ -> is_atomic_q q && is_ghorn_t t
    ApplTerm (QualOp Fun  (InstOpId i _ _) t _) arg _
        | (case arg of
          TupleTerm f@[f1, f2] _ ->
              t == logType &&
               (i == andId && (is_ghorn_c_conj f || is_ghorn_f_conj f)
                || i == implId && is_ghorn_prem f1 && is_ghorn_conc f2
                || i == eqvId && is_ghorn_prem f1 && is_ghorn_prem f2)
              || t == eqType && (i == exEq || i == eqId)
          _ -> False) || t == defType && i == defId
          -> True
     -- is_ghorn_t (Membership _ _ _) = True
    _ -> is_atomic_t term

-- C-CONJUNCTION
--
is_ghorn_c_conj :: [Term] -> Bool
is_ghorn_c_conj = and . map is_ghorn_conc

-- F-CONJUNCTION
--
is_ghorn_f_conj :: [Term] -> Bool
is_ghorn_f_conj = and . map is_ghorn_t

-- P-CONJUNCTION
--
is_ghorn_p_conj :: [Term] -> Bool
is_ghorn_p_conj = and . map is_ghorn_prem

-- PREMISE
is_ghorn_prem :: Term -> Bool
is_ghorn_prem term = case term of
    ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm ts@[_, _] _) _ ->
        i == andId && t == logType && is_ghorn_p_conj ts
    _ -> is_horn_p_a term

-- CONCLUSION
is_ghorn_conc :: Term -> Bool
is_ghorn_conc term = case term of
    ApplTerm (QualOp Fun  (InstOpId i _ _) t _) (TupleTerm ts@[_,_] _) _ ->
        i == andId && t == logType && is_ghorn_c_conj ts
    _ -> is_horn_a term

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
get_logic :: Term -> Sublogic
get_logic t = if (is_atomic_t t) then bottom else
                if (is_horn_t t) then need_horn else
                  if (is_ghorn_t t) then need_ghorn else
                    if (is_fol_t t) then need_fol else
                      need_hol

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element; these work
-- by recursing into all subelements
------------------------------------------------------------------------------

sl_basicSpec :: BasicSpec -> Sublogic
sl_basicSpec (BasicSpec l) = comp_list $ map sl_basicItem
                                       $ map item l

sl_basicItem :: BasicItem -> Sublogic
sl_basicItem bIt = case bIt of
    SigItems l -> sl_sigItems l
    ProgItems l _ -> comp_list $ map sl_progEq
                                         $ map item l
    ClassItems _ l _ -> (comp_list $ map sl_classItem
                                               $ map item l)
    GenVarItems l _ -> comp_list $ map sl_genVarDecl l
    FreeDatatype l _ -> comp_list $ map sl_datatypeDecl
                                            $ map item l
    GenItems l _ -> (comp_list $ map sl_sigItems
                                         $ map item l)
    AxiomItems l m _ -> sublogic_max
                                     (comp_list $ map sl_genVarDecl l)
                                     (comp_list $ map sl_term
                                                $ map item m)
    Internal l _ -> comp_list $ map sl_basicItem
                                        $ map item l

sl_sigItems :: SigItems -> Sublogic
sl_sigItems sIt = case sIt of
    TypeItems i l _ -> sublogic_max (sl_instance i)
                                  (comp_list $ map sl_typeItem
                                             $ map item l)
    OpItems b l _ -> sublogic_max (sl_opBrand b)
                                (comp_list $ map sl_opItem
                                           $ map item l)

sl_opBrand :: OpBrand -> Sublogic
sl_opBrand Pred = need_pred
sl_opBrand _ = bottom

sl_instance :: Instance -> Sublogic
sl_instance Instance = simpleTypeClasses
sl_instance _ = bottom

sl_classItem :: ClassItem -> Sublogic
sl_classItem (ClassItem c l _) = sublogic_max (sl_classDecl c)
                                   (comp_list $ map sl_basicItem
                                              $ map item l)

sl_classDecl :: ClassDecl -> Sublogic
sl_classDecl (ClassDecl _ k _) = case k of
    ClassKind _ -> simpleTypeClasses
    FunKind _ _ _ _ -> constructorClasses

sl_Rawkind :: RawKind -> Sublogic
sl_Rawkind (ClassKind _) = bottom
sl_Rawkind (FunKind _ _ _ _) = need_hol

sl_kind :: Kind -> Sublogic
sl_kind (ClassKind i) = if i == universeId then bottom else simpleTypeClasses
sl_kind (FunKind _ k1 k2 _) = comp_list [need_hol, (sl_kind k1), (sl_kind k2)]

sl_typeItem :: TypeItem -> Sublogic
sl_typeItem tyIt = case tyIt of
    TypeDecl l k _ -> sublogic_max (sl_kind k)
                                 (comp_list $ map sl_typePattern l)
    SubtypeDecl l _ _ -> sublogic_max need_sub
                                    (comp_list $ map sl_typePattern l)
    IsoDecl l _ -> sublogic_max need_sub
                              (comp_list $ map sl_typePattern l)
    SubtypeDefn tp _ t term _ ->
        comp_list [need_sub,
             (sl_typePattern tp),
             (sl_type t),
             (sl_term (item term))]
    AliasType tp (Just k) ts _ -> comp_list [(sl_kind k), (sl_typePattern tp),
                                             (sl_typeScheme ts)]
    AliasType tp Nothing ts _ -> sublogic_max (sl_typePattern tp)
                                                        (sl_typeScheme ts)
    Datatype dDecl -> sl_datatypeDecl dDecl

sl_typePattern :: TypePattern -> Sublogic
sl_typePattern tp = case tp of
    TypePattern _ l _ -> comp_list $ map sl_typeArg l
    -- non-empty args --> type constructor!
    MixfixTypePattern l -> comp_list $ map sl_typePattern l
    BracketTypePattern _ l _ -> comp_list $ map sl_typePattern l
    TypePatternArg _ _ -> need_polymorphism
    _ -> bottom

sl_type :: Type -> Sublogic
sl_type = sl_BasicFun

sl_Basictype :: Type -> Sublogic
sl_Basictype ty = case ty of
    TypeName _ k v -> sublogic_max
        (if v /= 0 then need_polymorphism else bottom) $ sl_Rawkind k
    KindedType t k _ -> sublogic_max (sl_Basictype t) $ sl_kind k
    ExpandedType _ t -> sl_Basictype t
    BracketType Parens [t] _ -> sl_Basictype t
    _ -> case getTypeAppl ty of
         (TypeName ide _ _, [_, _]) | isArrow ide ->
            sublogic_max need_ho $ sl_BasicFun ty
         (TypeName ide _ _, [arg]) | ide == lazyTypeId ->
            sublogic_max need_hol $ sl_Basictype arg
         (_, args) -> comp_list $ need_type_constructors :
                      map sl_Basictype args

sl_BasicProd :: Type -> Sublogic
sl_BasicProd ty = case getTypeAppl ty of
    (TypeName ide _ _, tyArgs@(_:_:_)) | ide == productId (length tyArgs)
        -> comp_list $ map sl_Basictype tyArgs
    _ -> sl_Basictype ty

sl_BasicFun :: Type -> Sublogic
sl_BasicFun ty = case getTypeAppl ty of
    (TypeName ide _ _, [arg, res]) | isArrow ide ->
           comp_list [if isPartialArrow ide then need_part else bottom,
              sl_BasicProd arg, sl_Basictype res]
    _ -> sl_Basictype ty

-- FOL, no higher types, all types are basic, tuples, or tuple -> basic
sl_typeScheme :: TypeScheme -> Sublogic
sl_typeScheme (TypeScheme l t _) =
  comp_list $ sl_type t : map sl_typeArg l

sl_opItem :: OpItem -> Sublogic
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

sl_partiality :: Partiality -> Sublogic
sl_partiality Partial = need_part
sl_partiality _ = bottom

sl_opAttr :: OpAttr -> Sublogic
sl_opAttr (UnitOpAttr t _) = sl_term t
sl_opAttr _ = need_eq

sl_datatypeDecl :: DatatypeDecl -> Sublogic
sl_datatypeDecl (DatatypeDecl t k l c _) =
  let sl = comp_list [(sl_typePattern t),
                      (sl_kind k),
                      (comp_list $ map sl_alternative
                                 $ map item l)]
  in
    if null c then sl
      else sublogic_max simpleTypeClasses sl

sl_alternative :: Alternative -> Sublogic
sl_alternative (Constructor _ l p _) =  sublogic_max (sl_partiality p)
                                          (comp_list $ map sl_component
                                                            (concat l))
sl_alternative (Subtype l _) = sublogic_max need_sub
                                 (comp_list $ map sl_type l)

sl_component :: Component -> Sublogic
sl_component (Selector _ p t _ _) =
   sublogic_max (sl_partiality p) (sl_type t)
sl_component (NoSelector t) = sl_type t

sl_term :: Term -> Sublogic
sl_term t = sublogic_max (get_logic t) (sl_t t)

sl_t :: Term -> Sublogic
sl_t (QualVar vd) = sl_varDecl vd
sl_t (QualOp b i t _) =
  comp_list [(sl_opBrand b),
             (sl_instOpId i),
             (sl_typeScheme t)]
--sl_t (ResolvedMixTerm _ l _) = comp_list $ map sl_t l
sl_t (ApplTerm t1 t2 _) = sublogic_max (sl_t t1) (sl_t t2)
sl_t (TupleTerm l _) = comp_list $ map sl_t l
sl_t (TypedTerm t _ ty _) = sublogic_max (sl_t t) (sl_type ty)
sl_t (QuantifiedTerm _ l t _) = sublogic_max (sl_t t)
                                 (comp_list $ map sl_genVarDecl l)
sl_t (LambdaTerm l p t _) =
  comp_list [(comp_list $ map sl_pattern l),
             (sl_partiality p),
             (sl_t t)]
sl_t (CaseTerm t l _) = sublogic_max (sl_t t)
                          (comp_list $ map sl_progEq l)
sl_t (LetTerm _ l t _) = sublogic_max (sl_t t)
                           (comp_list $ map sl_progEq l)
sl_t (MixTypeTerm _ t _) = sl_type t
sl_t (MixfixTerm l) = comp_list $ map sl_t l
sl_t (BracketTerm _ l _) = comp_list $ map sl_t l
sl_t (AsPattern vd p2 _) = sublogic_max (sl_varDecl vd) (sl_pattern p2)
sl_t _ = bottom

sl_pattern :: Pattern -> Sublogic
sl_pattern = sl_t

sl_progEq :: ProgEq -> Sublogic
sl_progEq (ProgEq p t _) = sublogic_max (sl_pattern p) (sl_t t)

sl_varDecl :: VarDecl -> Sublogic
sl_varDecl (VarDecl _ t _ _) = sl_type t

sl_varKind :: VarKind -> Sublogic
sl_varKind vk = case vk of
   VarKind k -> sl_kind k
   Downset t -> sublogic_max need_sub $ sl_type t
   _ -> bottom

sl_typeArg :: TypeArg -> Sublogic
sl_typeArg (TypeArg _ _ k _ _ _ _) =
    sublogic_max need_polymorphism (sl_varKind k)

sl_genVarDecl :: GenVarDecl -> Sublogic
sl_genVarDecl (GenVarDecl v) = sl_varDecl v
sl_genVarDecl (GenTypeVarDecl v) = sl_typeArg v

sl_opId :: OpId -> Sublogic
sl_opId (OpId _ l _) = comp_list $ map sl_typeArg l

sl_instOpId :: InstOpId -> Sublogic
sl_instOpId (InstOpId i l _) =
  if ((i == exEq) || (i == eqId))
    then sublogic_max need_eq (comp_list $ map sl_type l)
      else comp_list $ map sl_type l

sl_symbItems :: SymbItems -> Sublogic
sl_symbItems (SymbItems k l _ _) = sublogic_max (sl_symbKind k)
                                     (comp_list $ map sl_symb l)

sl_symbMapItems :: SymbMapItems -> Sublogic
sl_symbMapItems (SymbMapItems k l _ _) = sublogic_max (sl_symbKind k)
                                           (comp_list $ map sl_symbOrMap l)

sl_symbKind :: SymbKind -> Sublogic
sl_symbKind (SK_pred) = need_pred
sl_symbKind (SK_class) = simpleTypeClasses
sl_symbKind _ = bottom

sl_symb :: Symb -> Sublogic
sl_symb (Symb _ Nothing _) = bottom
sl_symb (Symb _ (Just l) _) = sl_symbType l

sl_symbType :: SymbType -> Sublogic
sl_symbType (SymbType t) = sl_typeScheme t

sl_symbOrMap :: SymbOrMap -> Sublogic
sl_symbOrMap (SymbOrMap s Nothing _) = sl_symb s
sl_symbOrMap (SymbOrMap s (Just t) _) =
  sublogic_max (sl_symb s) (sl_symb t)

-- the maps have no influence since all sorts,ops,preds in them
-- must also appear in the signatures, so any features needed by
-- them will be included by just checking the signatures
--

sl_env :: Env -> Sublogic
sl_env e =
    let classes = if Map.null $ classMap e
                    then bottom else simpleTypeClasses
        types = comp_list $ map sl_typeInfo (Map.elems (typeMap e))
        ops = comp_list $ map sl_opInfos (Map.elems (assumps e))
        in comp_list [classes, types, ops]

sl_typeInfo :: TypeInfo -> Sublogic
sl_typeInfo t = let s = sl_typeDefn (typeDefn t) in
                    if Set.null $ superTypes t then s else
                    sublogic_max need_sub  s

sl_typeDefn :: TypeDefn -> Sublogic
sl_typeDefn (DatatypeDefn de) = sl_dataEntry de
sl_typeDefn (AliasTypeDefn t) = sl_typeScheme t
sl_typeDefn _ = bottom

sl_dataEntry :: DataEntry -> Sublogic
sl_dataEntry (DataEntry _ _ _ l _ m) =
  sublogic_max (comp_list $ map sl_typeArg l)
                (comp_list $ map sl_altDefn m)

sl_opInfos :: OpInfos -> Sublogic
sl_opInfos o = comp_list $ map sl_opInfo (opInfos o)

sl_opInfo :: OpInfo -> Sublogic
sl_opInfo o = comp_list [(sl_typeScheme (opType o)),
                         (comp_list $ map sl_opAttr (opAttrs o)),
                         (sl_opDefn (opDefn o))]

sl_opDefn :: OpDefn -> Sublogic
sl_opDefn (NoOpDefn b) = sl_opBrand b
sl_opDefn (SelectData l _) = comp_list $ map sl_constrInfo l
sl_opDefn (Definition b t) =
  sublogic_max (sl_opBrand b) (sl_term t)
sl_opDefn _ = bottom

sl_constrInfo :: ConstrInfo -> Sublogic
sl_constrInfo c = sl_typeScheme (constrType c)

sl_sentence :: Sentence -> Sublogic
sl_sentence (Formula t) = sl_term t
sl_sentence (ProgEqSen _ ts pq) =
  sublogic_max (sl_typeScheme ts) (sl_progEq pq)
sl_sentence (DatatypeSen l) = comp_list $ map sl_dataEntry l

sl_altDefn :: AltDefn -> Sublogic
sl_altDefn (Construct _ l p m) =
  comp_list [(comp_list $ map sl_type l),
             (sl_partiality p),
             (comp_list $ map sl_selector $ concat m)]

sl_selector :: Selector -> Sublogic
sl_selector (Select _ t p) = sublogic_max (sl_type t)
                                           (sl_partiality p)

sl_morphism :: Morphism -> Sublogic
sl_morphism m = sublogic_max (sl_env $ msource m) (sl_env $ mtarget m)

sl_symbol :: Symbol -> Sublogic
sl_symbol (Symbol _ t e) =
  sublogic_max (sl_symbolType t) (sl_env e)

sl_symbolType :: SymbolType a -> Sublogic
sl_symbolType (OpAsItemType t) = sl_typeScheme t
sl_symbolType (ClassAsItemType _) = simpleTypeClasses
sl_symbolType _ = bottom

-- | check if the second sublogic is contained in the first sublogic
sl_in :: Sublogic -> Sublogic -> Bool
sl_in given new = sublogic_max given new == given

in_x :: Sublogic -> a -> (a -> Sublogic) -> Bool
in_x l x f = sl_in l (f x)

in_basicSpec :: Sublogic -> BasicSpec -> Bool
in_basicSpec l x = in_x l x sl_basicSpec

in_sentence :: Sublogic -> Sentence -> Bool
in_sentence l x = in_x l x sl_sentence

in_symbItems :: Sublogic -> SymbItems -> Bool
in_symbItems l x = in_x l x sl_symbItems

in_symbMapItems :: Sublogic -> SymbMapItems -> Bool
in_symbMapItems l x = in_x l x sl_symbMapItems

in_env :: Sublogic -> Env -> Bool
in_env l x = in_x l x sl_env

in_morphism :: Sublogic -> Morphism -> Bool
in_morphism l x = in_x l x sl_morphism

in_symbol :: Sublogic -> Symbol -> Bool
in_symbol l x = in_x l x sl_symbol

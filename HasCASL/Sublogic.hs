{- |
Module      :  $Header$
Description :  HasCASL's sublogics
Copyright   :  (c) Sonja Groening, C. Maeder, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs) for
  HasCASL. The functions allow to compute the minimal sublogic needed by a
  given element, to check whether an item is part of a given sublogic, and --
  not yet -- to project an element into a given sublogic.
-}

module HasCASL.Sublogic
    ( -- * datatypes
      Sublogic(..)
    , Formulas(..)
    , Classes(..)
      -- * functions for SemiLatticeWithTop instance
    , topLogic
    , sublogic_max
      -- * combining sublogics restrictions
    , sublogic_min
    , sublogicUp
    , need_hol
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

import qualified Data.Map as Map
import qualified Data.Set as Set
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
    { has_polymorphism = False
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
    , type_classes = NoClasses
    , has_polymorphism = False
    , has_type_constructors = False
    , which_logic = Atomic
    }

{- the following are used to add a needed feature to a given
   sublogic via sublogic_max, i.e. (sublogic_max given needs_part)
   will force partiality in addition to what features given already
   has included -}

-- | minimal sublogic with partiality
need_part :: Sublogic
need_part = bottom { has_part = True }

-- | minimal sublogic with equality
need_eq :: Sublogic
need_eq = bottom { has_eq = True }

-- | minimal sublogic with predicates
need_pred :: Sublogic
need_pred = bottom { has_pred = True }

-- | minimal sublogic with subsorting
need_sub :: Sublogic
need_sub = need_pred { has_sub = True }

-- | minimal sublogic with polymorhism
need_polymorphism :: Sublogic
need_polymorphism = bottom { has_polymorphism = True }

-- | minimal sublogic with simple type classes
simpleTypeClasses :: Sublogic
simpleTypeClasses = need_polymorphism { type_classes = SimpleTypeClasses }

-- | minimal sublogic with constructor classes
constructorClasses :: Sublogic
constructorClasses = need_polymorphism { type_classes = ConstructorClasses }

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
need_hol = need_pred { which_logic = HOL }

-- | make sublogic consistent w.r.t. illegal combinations
sublogicUp :: Sublogic -> Sublogic
sublogicUp s =
    if which_logic s == HOL || has_sub s then s { has_pred = True } else s

-- | generate a list of all sublogics for HasCASL
sublogics_all :: [Sublogic]
sublogics_all = let bools = [False, True] in
    [ Sublogic
    { has_sub = sub
    , has_part = part
    , has_eq = eq
    , has_pred = pre
    , type_classes = tyCl
    , has_polymorphism = poly
    , has_type_constructors = tyCon
    , which_logic = logic
    }
    | (tyCl, poly) <- [(NoClasses, False), (NoClasses, True),
                       (SimpleTypeClasses, True), (ConstructorClasses, True)]
    , tyCon <- bools
    , sub <- bools
    , part <- bools
    , eq <- bools
    , pre <- bools
    , logic <- [Atomic, Horn, GHorn, FOL, HOL]
    , pre || logic /= HOL && not sub
    ]

-- | conversion functions to String
formulas_name :: Bool -> Formulas -> String
formulas_name hasPred f = case f of
    HOL -> "HOL"
    FOL -> if hasPred then "FOL" else "FOAlg"
    _ -> case f of
         Atomic -> if hasPred then "Atom" else "Eq"
         _ -> (case f of
                GHorn -> ("G" ++)
                _ -> id) $ if hasPred then "Horn" else "Cond"

-- | the sublogic name as a singleton string list
sublogic_name :: Sublogic -> String
sublogic_name x =
     (if has_sub x then "Sub" else "")
  ++ (if has_part x then "P" else "")
  ++ (case type_classes x of
         NoClasses -> if has_polymorphism x then "Poly" else ""
         SimpleTypeClasses -> "TyCl"
         ConstructorClasses -> "CoCl")
  ++ (if has_type_constructors x then "TyCons" else "")
  ++ formulas_name (has_pred x) (which_logic x)
  ++ (if has_eq x then "=" else "")

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
comp_list = foldl sublogic_max bottom

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
    , foldQualOp = \ _ b (PolyId i _ _) t _ _ _ ->
                   b /= Fun && notElem (i, t) bList
    , foldApplTerm = \ _ b1 b2 _ -> b1 && b2
    , foldTupleTerm = \ _ bs _ -> and bs
    , foldTypedTerm = \ _ b q _ _ -> q /= InType && b
    , foldAsPattern = \ _ _ _ _ -> False
    , foldQuantifiedTerm = \ _ _ _ _ _ -> False
    , foldLambdaTerm = \ _ _ _ _ _ -> False
    , foldCaseTerm = \ _ _ _ _ -> False
    , foldLetTerm = \ _ _ _ _ _ -> False
    , foldResolvedMixTerm = \ _ i _ bs _ ->
          notElem i (map fst bList) && and bs
    , foldTermToken = \ _ _ -> True
    , foldMixTypeTerm = \ _ q _ _ -> q /= InType
    , foldMixfixTerm = const and
    , foldBracketTerm = \ _ _ bs _ -> and bs
    , foldProgEq = \ _ _ _ _ -> False
    }

-- FORMULA, P-ATOM
is_atomic_t :: Term -> Bool
is_atomic_t term = case term of
    QuantifiedTerm q _ t _ | is_atomic_q q && is_atomic_t t -> True
      -- P-Conjunction and ExEq
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) arg _
      | (case arg of
        TupleTerm ts@[_, _] _ ->
            i == andId && t == logType && all is_atomic_t ts
            || i == exEq && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    QualOp _ (PolyId i _ _) t _ _ _
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
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) (TupleTerm [t1, t2] _) _
        | i == implId && t == logType && is_horn_p_conj t1 && is_horn_a t2
          -> True
    _ -> is_atomic_t term

-- P-CONJUNCTION
is_horn_p_conj :: Term -> Bool
is_horn_p_conj term = case term of
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) (TupleTerm ts@[_, _] _) _
        | i == andId && t == logType && all is_horn_a ts
          -> True
    _ -> is_atomic_t term

-- ATOM
is_horn_a :: Term -> Bool
is_horn_a term = case term of
    QualOp _ (PolyId i _ _) t _ _ _
        | i == trueId && t == unitTypeScheme -> True
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) arg _
      | (case arg of
        TupleTerm [_, _] _ -> (i == exEq || i == eqId) && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    _ -> is_atomic_t term

-- P-ATOM
is_horn_p_a :: Term -> Bool
is_horn_p_a term = case term of
    QualOp _ (PolyId i _ _) t _ _ _
        | i == trueId && t == unitTypeScheme -> True
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) arg _
      | (case arg of
        TupleTerm [_, _] _ -> i == exEq && t == eqType
        _ -> False) || i == defId && t == defType
        -> True
    _ -> is_atomic_t term

-- Generalized Positive Conditional Logic (subsection 3.3 of the paper)

-- FORMULA, ATOM
is_ghorn_t :: Term -> Bool
is_ghorn_t term = case term of
    QuantifiedTerm q _ t _ -> is_atomic_q q && is_ghorn_t t
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) arg _
        | (case arg of
          TupleTerm f@[f1, f2] _ ->
              t == logType &&
               (i == andId && (is_ghorn_c_conj f || is_ghorn_f_conj f)
                || i == implId && is_ghorn_prem f1 && is_ghorn_conc f2
                || i == eqvId && is_ghorn_prem f1 && is_ghorn_prem f2)
              || t == eqType && (i == exEq || i == eqId)
          _ -> False) || t == defType && i == defId
          -> True
    _ -> is_atomic_t term

-- C-CONJUNCTION
--
is_ghorn_c_conj :: [Term] -> Bool
is_ghorn_c_conj = all is_ghorn_conc

-- F-CONJUNCTION
--
is_ghorn_f_conj :: [Term] -> Bool
is_ghorn_f_conj = all is_ghorn_t

-- P-CONJUNCTION
--
is_ghorn_p_conj :: [Term] -> Bool
is_ghorn_p_conj = all is_ghorn_prem

-- PREMISE
is_ghorn_prem :: Term -> Bool
is_ghorn_prem term = case term of
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) (TupleTerm ts@[_, _] _) _ ->
        i == andId && t == logType && is_ghorn_p_conj ts
    _ -> is_horn_p_a term

-- CONCLUSION
is_ghorn_conc :: Term -> Bool
is_ghorn_conc term = case term of
    ApplTerm (QualOp _ (PolyId i _ _) t _ _ _) (TupleTerm ts@[_,_] _) _ ->
        i == andId && t == logType && is_ghorn_c_conj ts
    _ -> is_horn_a term

is_fol_t :: Term -> Bool
is_fol_t t = case t of
    LambdaTerm _ _ _ _ -> False
    CaseTerm _ _ _ -> False
    LetTerm _ _ _ _ -> False
    _ -> True
{- FOL:
  no lambda/let/case,
  no higher types (i.e. all types are basic, tuples, or tuple -> basic)
-}

-- | compute logic of a formula by checking all logics in turn
get_logic :: Term -> Sublogic
get_logic t
  | is_atomic_t t = bottom
  | is_horn_t t = need_horn
  | is_ghorn_t t = need_ghorn
  | is_fol_t t = need_fol
  | otherwise = need_hol

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element; these work
-- by recursing into all subelements
------------------------------------------------------------------------------

sl_basicSpec :: BasicSpec -> Sublogic
sl_basicSpec (BasicSpec l) =
    sublogicUp $ comp_list $ map (sl_basicItem . item) l

sl_basicItem :: BasicItem -> Sublogic
sl_basicItem bIt = case bIt of
    SigItems l -> sl_sigItems l
    ProgItems l _ -> comp_list $ map (sl_progEq . item) l
    ClassItems _ l _ -> comp_list $ map (sl_classItem . item) l
    GenVarItems l _ -> comp_list $ map sl_genVarDecl l
    FreeDatatype l _ -> comp_list $ map (sl_datatypeDecl . item) l
    GenItems l _ -> comp_list $ map (sl_sigItems . item) l
    AxiomItems l m _ ->
        comp_list $ map sl_genVarDecl l ++ map (sl_term . item) m
    Internal l _ -> comp_list $ map (sl_basicItem . item) l

sl_sigItems :: SigItems -> Sublogic
sl_sigItems sIt = case sIt of
    TypeItems i l _ ->
        comp_list $ sl_instance i : map (sl_typeItem . item) l
    OpItems b l _ ->
        comp_list $ sl_opBrand b : map (sl_opItem . item) l

sl_opBrand :: OpBrand -> Sublogic
sl_opBrand o = case o of
    Pred -> need_pred
    _ -> bottom

sl_instance :: Instance -> Sublogic
sl_instance i = case i of
    Instance -> simpleTypeClasses
    _ -> bottom

sl_classItem :: ClassItem -> Sublogic
sl_classItem (ClassItem c l _) =
    comp_list $ sl_classDecl c : map (sl_basicItem . item) l

sl_classDecl :: ClassDecl -> Sublogic
sl_classDecl (ClassDecl _ k _) = case k of
    ClassKind _ -> simpleTypeClasses
    FunKind _ _ _ _ -> constructorClasses

-- don't check the variance or kind of builtin type constructors
sl_Variance :: Variance -> Sublogic
sl_Variance v = case v of
    NonVar -> bottom
    _ -> need_sub

sl_AnyKind :: (a -> Sublogic) -> AnyKind a -> Sublogic
sl_AnyKind f k = case k of
   ClassKind i -> f i
   FunKind v k1 k2 _ ->
       comp_list [sl_Variance v, sl_AnyKind f k1, sl_AnyKind f k2]

sl_Rawkind :: RawKind -> Sublogic
sl_Rawkind = sl_AnyKind (const bottom)

sl_kind :: Kind -> Sublogic
sl_kind = sl_AnyKind $
          \ i -> if i == universeId then bottom else simpleTypeClasses

sl_typeItem :: TypeItem -> Sublogic
sl_typeItem tyIt = case tyIt of
    TypeDecl l k _ -> comp_list $ sl_kind k : map sl_typePattern l
    SubtypeDecl l _ _ -> comp_list $ need_sub : map sl_typePattern l
    IsoDecl l _ -> comp_list $ need_sub : map sl_typePattern l
    SubtypeDefn tp _ t term _ -> comp_list
        [ need_sub
        , sl_typePattern tp
        , sl_type t
        , sl_term $ item term ]
    AliasType tp (Just k) ts _ -> comp_list
        [ sl_kind k
        , sl_typePattern tp
        , sl_typeScheme ts ]
    AliasType tp Nothing ts _ ->
        sublogic_max (sl_typePattern tp) $ sl_typeScheme ts
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
    KindedType t k _ -> comp_list $ sl_Basictype t : map sl_kind (Set.toList k)
    ExpandedType _ t -> sl_Basictype t
    TypeAbs v t _ -> comp_list
        [ need_type_constructors
        , sl_typeArg v
        , sl_Basictype t ]
    BracketType Parens [t] _ -> sl_Basictype t
    _ -> case getTypeAppl ty of
         (TypeName ide _ _, args) -> comp_list $
            (if isArrow ide || ide == lazyTypeId then need_hol else
                need_type_constructors) : map sl_Basictype args
         (_, []) -> error "sl_Basictype"
         (t, args) -> comp_list $ sl_Basictype t : map sl_Basictype args

sl_BasicProd :: Type -> Sublogic
sl_BasicProd ty = case getTypeAppl ty of
    (TypeName ide _ _, tyArgs@(_ : _ : _))
        | isProductIdWithArgs ide $ length tyArgs
        -> comp_list $ map sl_Basictype tyArgs
    _ -> sl_Basictype ty

sl_BasicFun :: Type -> Sublogic
sl_BasicFun ty = case getTypeAppl ty of
    (TypeName ide _ _, [arg, res]) | isArrow ide -> comp_list
        [ if isPartialArrow ide then need_part else bottom
        , sl_BasicProd arg
        , sl_Basictype res ]
    _ -> sl_Basictype ty

-- FOL, no higher types, all types are basic, tuples, or tuple -> basic
sl_typeScheme :: TypeScheme -> Sublogic
sl_typeScheme (TypeScheme l t _) = comp_list $ sl_type t : map sl_typeArg l

sl_opItem :: OpItem -> Sublogic
sl_opItem o = case o of
    OpDecl l t m _ -> comp_list $
        sl_typeScheme t : map sl_opId l ++ map sl_opAttr m
    OpDefn i v ts t _ -> comp_list $
        [ sl_opId i
        , sl_typeScheme ts
        , sl_term t
        ] ++ map sl_varDecl (concat v)

sl_partiality :: Partiality -> Sublogic
sl_partiality p = case p of
    Partial -> need_part
    Total -> bottom

sl_opAttr :: OpAttr -> Sublogic
sl_opAttr a = case a of
    UnitOpAttr t _ -> sl_term t
    _ -> need_eq

sl_datatypeDecl :: DatatypeDecl -> Sublogic
sl_datatypeDecl (DatatypeDecl t k l c _) = comp_list $
    [ if null c then bottom else simpleTypeClasses
    , sl_typePattern t
    , sl_kind k ] ++ map (sl_alternative . item) l

sl_alternative :: Alternative -> Sublogic
sl_alternative a = case a of
    Constructor _ l p _ ->
        comp_list $ sl_partiality p : map sl_component (concat l)
    Subtype l _ -> comp_list $ need_sub : map sl_type l

sl_component :: Component -> Sublogic
sl_component s = case s of
    Selector _ p t _ _ -> sublogic_max (sl_partiality p) $ sl_type t
    NoSelector t -> sl_type t

sl_term :: Term -> Sublogic
sl_term t = sublogic_max (get_logic t) $ sl_t t

-- typed in- or as-terms would also indicate subtyping
-- but we rely on the subtypes in the signature
sl_t :: Term -> Sublogic
sl_t trm = case trm of
    QualVar vd -> sl_varDecl vd
    QualOp b i t _ _ _ -> comp_list
        [ sl_opBrand b
        , sl_opId i
        , sl_typeScheme t ]
    ApplTerm t1 t2 _ -> sublogic_max (sl_t t1) $ sl_t t2
    TupleTerm l _ -> comp_list $ map sl_t l
    TypedTerm t _ ty _ -> sublogic_max (sl_t t) $ sl_type ty
    QuantifiedTerm _ l t _ -> comp_list $ sl_t t : map sl_genVarDecl l
    LambdaTerm l p t _ ->
        comp_list $ sl_partiality p : sl_t t : map sl_t l
    CaseTerm t l _ -> comp_list $ sl_t t : map sl_progEq l ++ map sl_progEq l
    LetTerm _ l t _ -> comp_list $ sl_t t : map sl_progEq l
    MixTypeTerm _ t _ -> sl_type t
    MixfixTerm l -> comp_list $ map sl_t l
    BracketTerm _ l _ -> comp_list $ map sl_t l
    AsPattern vd p2 _ -> sublogic_max (sl_varDecl vd) $ sl_t p2
    _ -> bottom

sl_progEq :: ProgEq -> Sublogic
sl_progEq (ProgEq p t _) = sublogic_max (sl_t p) (sl_t t)

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
sl_genVarDecl g = case g of
    GenVarDecl v -> sl_varDecl v
    GenTypeVarDecl v -> sl_typeArg v

sl_opId :: PolyId -> Sublogic
sl_opId (PolyId i tys _) = if i == exEq || i == eqId then need_eq else
    comp_list $ map sl_typeArg tys

sl_symbItems :: SymbItems -> Sublogic
sl_symbItems (SymbItems k l _ _) = comp_list $ sl_symbKind k : map sl_symb l

sl_symbMapItems :: SymbMapItems -> Sublogic
sl_symbMapItems (SymbMapItems k l _ _) =
    comp_list $ sl_symbKind k : map sl_symbOrMap l

sl_symbKind :: SymbKind -> Sublogic
sl_symbKind k = case k of
    SyKpred -> need_pred
    SyKclass -> simpleTypeClasses
    _ -> bottom

sl_symb :: Symb -> Sublogic
sl_symb s = case s of
    Symb _ Nothing _ -> bottom
    Symb _ (Just l) _ -> sl_symbType l

sl_symbType :: SymbType -> Sublogic
sl_symbType (SymbType t) = sl_typeScheme t

sl_symbOrMap :: SymbOrMap -> Sublogic
sl_symbOrMap m = case m of
    SymbOrMap s Nothing _ -> sl_symb s
    SymbOrMap s (Just t) _ -> sublogic_max (sl_symb s) $ sl_symb t

{- the maps have no influence since all sorts,ops,preds in them
   must also appear in the signatures, so any features needed by
   them will be included by just checking the signatures -}

sl_env :: Env -> Sublogic
sl_env e = sublogicUp $ comp_list $
    (if Map.null $ classMap e then bottom else simpleTypeClasses)
    : map sl_typeInfo (Map.elems $ typeMap e)
    ++ map sl_opInfos (Map.elems $ assumps e)

sl_typeInfo :: TypeInfo -> Sublogic
sl_typeInfo t =
    sublogic_max (if Set.null $ superTypes t then bottom else need_sub)
    $ sl_typeDefn $ typeDefn t

sl_typeDefn :: TypeDefn -> Sublogic
sl_typeDefn d = case d of
    DatatypeDefn de -> sl_dataEntry de
    AliasTypeDefn t -> sl_type t
    _ -> bottom

sl_dataEntry :: DataEntry -> Sublogic
sl_dataEntry (DataEntry _ _ _ l _ m) =
    comp_list $ map sl_typeArg l ++ map sl_altDefn (Set.toList m)

sl_opInfos :: Set.Set OpInfo -> Sublogic
sl_opInfos = comp_list . map sl_opInfo . Set.toList

sl_opInfo :: OpInfo -> Sublogic
sl_opInfo o = comp_list $ sl_typeScheme (opType o) : sl_opDefn (opDefn o)
              : map sl_opAttr (Set.toList $ opAttrs o)

sl_opDefn :: OpDefn -> Sublogic
sl_opDefn o = case o of
    NoOpDefn b -> sl_opBrand b
    SelectData l _ -> comp_list $ map sl_constrInfo $ Set.toList l
    Definition b t -> sublogic_max (sl_opBrand b) $ sl_term t
    _ -> bottom

sl_constrInfo :: ConstrInfo -> Sublogic
sl_constrInfo = sl_typeScheme . constrType

sl_sentence :: Sentence -> Sublogic
sl_sentence s = sublogicUp $ case s of
    Formula t -> sl_term t
    ProgEqSen _ ts pq -> sublogic_max (sl_typeScheme ts) $ sl_progEq pq
    DatatypeSen l -> comp_list $ map sl_dataEntry l

-- a missing constructor identifier also indicates subtyping
-- but checking super types is enough for subtype detection
sl_altDefn :: AltDefn -> Sublogic
sl_altDefn (Construct _ l p m) = comp_list $ sl_partiality p :
    map sl_type l ++ map sl_selector (concat m)

sl_selector :: Selector -> Sublogic
sl_selector (Select _ t p) = sublogic_max (sl_type t) $ sl_partiality p

sl_morphism :: Morphism -> Sublogic
sl_morphism m = sublogic_max (sl_env $ msource m) $ sl_env $ mtarget m

sl_symbol :: Symbol -> Sublogic
sl_symbol (Symbol _ t e) = sublogic_max (sl_symbolType t) $ sl_env e

sl_symbolType :: SymbolType a -> Sublogic
sl_symbolType s = case s of
    OpAsItemType t -> sl_typeScheme t
    ClassAsItemType _ -> simpleTypeClasses
    _ -> bottom

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

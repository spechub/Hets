{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HasCASL/As.hs
Description :  abstract syntax for HasCASL
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

abstract syntax for HasCASL,
   more liberal than Concrete-Syntax.txt,
   annotations are almost as for CASL
-}

module HasCASL.As where

import Common.Id
import Common.Keywords
import Common.AS_Annotation

import Data.Data
import qualified Data.Set as Set

import Common.Doc
import Common.DocUtils

-- * abstract syntax entities with small utility functions

-- | annotated basic items
data BasicSpec = BasicSpec [Annoted BasicItem] deriving (Show, Typeable, Data)

-- | the possible items
data BasicItem =
    SigItems SigItems
  | ProgItems [Annoted ProgEq] Range
  -- pos "program", dots
  | ClassItems Instance [Annoted ClassItem] Range
  -- pos "class", ";"s
  | GenVarItems [GenVarDecl] Range
  -- pos "var", ";"s
  | FreeDatatype [Annoted DatatypeDecl] Range
  -- pos "free", "type", ";"s
  | GenItems [Annoted SigItems] Range
  {- pos "generated" "{", ";"s, "}"
  or "generated" "type" ";"s -}
  | AxiomItems [GenVarDecl] [Annoted Term] Range
  -- pos "forall" (if GenVarDecl not empty), dots
  | Internal [Annoted BasicItem] Range
    -- pos "internal" "{", ";"s, "}"
    deriving (Show, Typeable, Data)

-- | signature items are types or functions
data SigItems =
    TypeItems Instance [Annoted TypeItem] Range {- including sort
    pos "type", ";"s -}
  | OpItems OpBrand [Annoted OpItem] Range
    -- pos "op", ";"s
    deriving (Show, Typeable, Data)

-- | indicator for predicate, operation or function
data OpBrand = Pred | Op | Fun deriving (Eq, Ord, Typeable, Data)

-- | test if the function was declared as predicate
isPred :: OpBrand -> Bool
isPred b = case b of
    Pred -> True
    _ -> False

instance Show OpBrand where
    show b = case b of
        Pred -> predS
        Op -> opS
        Fun -> functS

-- | indicator in 'ClassItems' and 'TypeItems'
data Instance = Instance | Plain deriving (Eq, Ord, Typeable, Data)

instance Show Instance where
    show i = case i of
        Instance -> instanceS
        Plain -> ""

-- | a class item
data ClassItem = ClassItem ClassDecl [Annoted BasicItem] Range
  deriving (Show, Typeable, Data)
                 -- pos "{", ";"s "}"

-- | declaring class identifiers
data ClassDecl = ClassDecl [Id] Kind Range deriving (Show, Typeable, Data)
               -- pos ","s

-- | co- or contra- variance indicator
data Variance = InVar | CoVar | ContraVar | NonVar
  deriving (Eq, Ord, Typeable, Data)

instance Show Variance where
    show v = case v of
        InVar -> plusS ++ minusS
        CoVar -> plusS
        ContraVar -> minusS
        NonVar -> ""

-- | (higher) kinds
data AnyKind a =
    ClassKind a
  | FunKind Variance (AnyKind a) (AnyKind a) Range
    -- pos "+" or "-"
    deriving (Show, Typeable, Data)

instance Ord a => Eq (AnyKind a) where
   k1 == k2 = compare k1 k2 == EQ

instance Ord a => Ord (AnyKind a) where
   compare k1 k2 = case (k1, k2) of
       (ClassKind c1, ClassKind c2) -> compare c1 c2
       (ClassKind _, _) -> LT
       (FunKind v1 k3 k4 _, FunKind v2 k5 k6 _) ->
           compare (v1, k3, k4) (v2, k5, k6)
       _ -> GT

type Kind = AnyKind Id
type RawKind = AnyKind ()

-- | the possible type items
data TypeItem =
    TypeDecl [TypePattern] Kind Range
    -- pos ","s
  | SubtypeDecl [TypePattern] Type Range
  -- pos ","s, "<"
  | IsoDecl [TypePattern] Range
  -- pos "="s
  | SubtypeDefn TypePattern Vars Type (Annoted Term) Range
  -- pos "=", "{", ":", dot, "}"
  | AliasType TypePattern (Maybe Kind) TypeScheme Range
  -- pos ":="
  | Datatype DatatypeDecl
    deriving (Show, Typeable, Data)

-- | a tuple pattern for 'SubtypeDefn'
data Vars = Var Id | VarTuple [Vars] Range
  deriving (Show, Eq, Ord, Typeable, Data)

-- | the lhs of most type items
data TypePattern =
    TypePattern Id [TypeArg] Range
    -- pos "("s, ")"s
  | TypePatternToken Token
  | MixfixTypePattern [TypePattern]
  | BracketTypePattern BracketKind [TypePattern] Range
  -- pos brackets (no parenthesis)
  | TypePatternArg TypeArg Range
    -- pos "(", ")"
    deriving (Show, Typeable, Data)

-- | types based on variable or constructor names and applications
data Type =
    TypeName Id RawKind Int
    -- Int == 0 means constructor, negative are bound variables
  | TypeAppl Type Type
  | ExpandedType Type Type    {- an alias type with its expansion
  only the following variants are parsed -}
  | TypeAbs TypeArg Type Range
  | KindedType Type (Set.Set Kind) Range
  -- pos ":"
  | TypeToken Token
  | BracketType BracketKind [Type] Range
  -- pos "," (between type arguments)
  | MixfixType [Type]
    deriving (Show, Typeable, Data)

-- | change the type within a scheme
mapTypeOfScheme :: (Type -> Type) -> TypeScheme -> TypeScheme
mapTypeOfScheme f (TypeScheme args t ps) = TypeScheme args (f t) ps

{- | a type with bound type variables. The bound variables within the
scheme should have negative numbers in the order given by the type
argument list. The type arguments store proper kinds (including
downsets) whereas the kind within the type names are only raw
kinds. -}
data TypeScheme = TypeScheme [TypeArg] Type Range
  deriving (Show, Eq, Ord, Typeable, Data)
    {- pos "forall", ";"s,  dot (singleton list)
    pos "\" "("s, ")"s, dot for type aliases -}

-- | indicator for partial or total functions
data Partiality = Partial | Total deriving (Eq, Ord, Typeable, Data)

instance Show Partiality where
    show p = case p of
        Partial -> quMark
        Total -> exMark

-- | function declarations or definitions
data OpItem =
    OpDecl [PolyId] TypeScheme [OpAttr] Range
    -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
  | OpDefn PolyId [[VarDecl]] TypeScheme Term Range
    -- pos "("s, ";"s, ")"s, ":" and "="
    deriving (Show, Typeable, Data)

-- | attributes without arguments for binary functions
data BinOpAttr = Assoc | Comm | Idem deriving (Eq, Ord, Typeable, Data)

instance Show BinOpAttr where
    show a = case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

-- | possible function attributes (including a term as a unit element)
data OpAttr =
    BinOpAttr BinOpAttr Range
  | UnitOpAttr Term Range deriving (Show, Typeable, Data)

instance Eq OpAttr where
    o1 == o2 = compare o1 o2 == EQ

instance Ord OpAttr where
    compare o1 o2 = case (o1, o2) of
        (BinOpAttr b1 _, BinOpAttr b2 _) -> compare b1 b2
        (BinOpAttr _ _, _) -> LT
        (UnitOpAttr t1 _, UnitOpAttr t2 _) -> compare t1 t2
        _ -> GT

-- | a polymorphic data type declaration with a deriving clause
data DatatypeDecl =
    DatatypeDecl TypePattern Kind [Annoted Alternative] [Id] Range
    -- pos "::=", "|"s, "deriving"
    deriving (Show, Typeable, Data)

{- | Alternatives are subtypes or a constructor with a list of
(curried) tuples as arguments. Only the components of the first tuple
can be addressed by the places of the mixfix constructor. -}
data Alternative =
    Constructor Id [[Component]] Partiality Range
    -- pos: "("s, ";"s, ")"s, "?"
  | Subtype [Type] Range
    -- pos: "type", ","s
    deriving (Show, Typeable, Data)

{- | A component is a type with on optional (only pre- or postfix)
   selector function. -}
data Component =
    Selector Id Partiality Type SeparatorKind Range
    -- pos ",", ":" or ":?"
  | NoSelector Type
    deriving (Show, Eq, Ord, Typeable, Data)

-- | the possible quantifiers
data Quantifier = Universal | Existential | Unique
  deriving (Show, Eq, Ord, Typeable, Data)

-- | the possibly type annotations of terms
data TypeQual = OfType | AsType | InType | Inferred
  deriving (Show, Eq, Ord, Typeable, Data)

-- | an indicator of (otherwise equivalent) let or where equations
data LetBrand = Let | Where | Program deriving (Show, Eq, Ord, Typeable, Data)

-- | the possible kinds of brackets (that should match when parsed)
data BracketKind = Parens | Squares | Braces | NoBrackets
  deriving (Show, Eq, Ord, Typeable, Data)

-- | the brackets as strings for printing
getBrackets :: BracketKind -> (String, String)
getBrackets b = case b of
    Parens -> ("(", ")")
    Squares -> ("[", "]")
    Braces -> ("{", "}")
    NoBrackets -> ("", "") -- for printing only

data InstKind = UserGiven | Infer deriving (Show, Eq, Ord, Typeable, Data)

{- | The possible terms and patterns. Formulas are also kept as
terms. Local variables and constants are kept separatetly. The variant
'ResolvedMixTerm' is an intermediate representation for type checking
only. -}
data Term =
    QualVar VarDecl
    -- pos "(", "var", ":", ")"
  | QualOp OpBrand PolyId TypeScheme [Type] InstKind Range
  -- pos "(", "op", ":", ")"
  | ApplTerm Term Term Range  {- analysed
  pos? -}
  | TupleTerm [Term] Range    {- special application
  pos "(", ","s, ")" -}
  | TypedTerm Term TypeQual Type Range
  -- pos ":", "as" or "in"
  | AsPattern VarDecl Term Range
  {- pos "@"
  patterns are terms constructed by the first six variants -}
  | QuantifiedTerm Quantifier [GenVarDecl] Term Range
  {- pos quantifier, ";"s, dot
  only "forall" may have a TypeVarDecl -}
  | LambdaTerm [Term] Partiality Term Range
  -- pos "\", dot (plus "!")
  | CaseTerm Term [ProgEq] Range
  -- pos "case", "of", "|"s
  | LetTerm LetBrand [ProgEq] Term Range
  -- pos "where", ";"s
  | ResolvedMixTerm Id [Type] [Term] Range
  | TermToken Token
  | MixTypeTerm TypeQual Type Range
  | MixfixTerm [Term]
  | BracketTerm BracketKind [Term] Range
    -- pos brackets, ","s
    deriving (Show, Eq, Ord, Typeable, Data)

-- | an equation or a case as pair of a pattern and a term
data ProgEq = ProgEq Term Term Range deriving (Show, Eq, Ord, Typeable, Data)
            -- pos "=" (or "->" following case-of)

-- | an identifier with an optional list of type declarations
data PolyId = PolyId Id [TypeArg] Range deriving (Show, Eq, Ord, Typeable, Data)
              -- pos "[", ",", "]"

{- | an indicator if variables were separated by commas or by separate
declarations -}
data SeparatorKind = Comma | Other deriving (Show, Typeable, Data)

-- ignore all separator kinds in comparisons
instance Eq SeparatorKind where
    _ == _ = True

-- Ord must be consistent with Eq
instance Ord SeparatorKind where
   compare _ _ = EQ

-- | a variable with its type
data VarDecl = VarDecl Id Type SeparatorKind Range
  deriving (Show, Eq, Ord, Typeable, Data)
               -- pos "," or ":"

-- | the kind of a type variable (or a type argument in schemes)
data VarKind = VarKind Kind | Downset Type | MissingKind
 deriving (Show, Eq, Ord, Typeable, Data)

-- | a (simple) type variable with its kind (or supertype)
data TypeArg =
    TypeArg Id Variance VarKind RawKind Int SeparatorKind Range
    -- pos "," or ":", "+" or "-"
    deriving (Show, Typeable, Data)

-- | a value or type variable
data GenVarDecl =
    GenVarDecl VarDecl
  | GenTypeVarDecl TypeArg
    deriving (Show, Eq, Ord, Typeable, Data)

{- * symbol data types
symbols -}
data SymbItems =
    SymbItems SymbKind [Symb] [Annotation] Range
  deriving (Show, Eq, Ord, Typeable, Data)
    -- pos: kind, commas

-- | mapped symbols
data SymbMapItems =
    SymbMapItems SymbKind [SymbOrMap] [Annotation] Range
  deriving (Show, Eq, Ord, Typeable, Data)
    -- pos: kind commas

-- | kind of symbols
data SymbKind =
    Implicit
  | SyKtype
  | SyKsort
  | SyKfun
  | SyKop
  | SyKpred
  | SyKclass
    deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty SymbKind where
  pretty symbol_kind = case symbol_kind of
    Implicit -> text "implicit"
    SyKtype -> text "type"
    SyKsort -> text "sort"
    SyKfun -> text "fun"
    SyKop -> text "op"
    SyKpred -> text "pred"
    SyKclass -> text "class"
    
-- | type annotated symbols
data Symb = Symb Id (Maybe SymbType) Range
  deriving (Show, Eq, Ord, Typeable, Data)
            -- pos: colon (or empty)

-- | type for symbols
data SymbType = SymbType TypeScheme deriving (Show, Eq, Ord, Typeable, Data)

-- | mapped symbol
data SymbOrMap = SymbOrMap Symb (Maybe Symb) Range
  deriving (Show, Eq, Ord, Typeable, Data)
                   -- pos: "|->" (or empty)

-- * equality instances ignoring positions

instance Eq Type where
    t1 == t2 = compare t1 t2 == EQ

instance Ord Type where
  compare ty1 ty2 = case (ty1, ty2) of
    (TypeName i1 k1 v1, TypeName i2 k2 v2) ->
        if v1 == 0 && v2 == 0 then compare (i1, k1) (i2, k2)
        else compare (v1, k1) (v2, k2)
    (TypeAppl f1 a1, TypeAppl f2 a2) -> compare (f1, a1) (f2, a2)
    (TypeAbs v1 a1 _, TypeAbs v2 a2 _) -> compare (v1, a1) (v2, a2)
    (TypeToken t1, TypeToken t2) -> compare t1 t2
    (BracketType b1 l1 _, BracketType b2 l2 _) -> compare (b1, l1) (b2, l2)
    (KindedType t1 k1 _, KindedType t2 k2 _) -> compare (t1, k1) (t2, k2)
    (MixfixType l1, MixfixType l2) -> compare l1 l2
    (ExpandedType _ t1, t2) -> compare t1 t2
    (t1, ExpandedType _ t2) -> compare t1 t2
    (TypeName {}, _) -> LT
    (_, TypeName {}) -> GT
    (TypeAppl {}, _) -> LT
    (_, TypeAppl {}) -> GT
    (TypeAbs {}, _) -> LT
    (_, TypeAbs {}) -> GT
    (TypeToken _, _) -> LT
    (_, TypeToken _) -> GT
    (BracketType {}, _) -> LT
    (_, BracketType {}) -> GT
    (KindedType {}, _) -> LT
    (_, KindedType {}) -> GT

-- used within quantified formulas
instance Eq TypeArg where
    t1 == t2 = compare t1 t2 == EQ
instance Ord TypeArg where
    compare (TypeArg i1 v1 e1 r1 c1 _ _) (TypeArg i2 v2 e2 r2 c2 _ _) =
        if c1 < 0 && c2 < 0 then compare (v1, e1, r1, c1) (v2, e2, r2, c2)
        else compare (i1, v1, e1, r1, c1) (i2, v2, e2, r2, c2)

-- * compute better position

-- | get a reasonable position for a list with an additional position list
bestRange :: GetRange a => [a] -> Range -> Range
bestRange l (Range ps) = Range (rangeToList (getRange l) ++ ps)

instance GetRange OpAttr where
  getRange a = case a of
    BinOpAttr _ r -> r
    UnitOpAttr _ r -> r

instance GetRange Type where
  getRange ty = case ty of
    TypeName i _ _ -> posOfId i
    TypeAppl t1 t2 -> getRange [t1, t2]
    TypeAbs _ t ps -> bestRange [t] ps
    ExpandedType t1 t2 -> getRange [t1, t2]
    TypeToken t -> tokPos t
    BracketType _ ts ps -> bestRange ts ps
    KindedType t _ ps -> bestRange [t] ps
    MixfixType ts -> getRange ts

instance GetRange Term where
   getRange trm = case trm of
    QualVar v -> getRange v
    QualOp _ (PolyId i _ _) _ _ _ qs -> bestRange [i] qs
    ResolvedMixTerm i _ _ _ -> posOfId i
    ApplTerm t1 t2 ps -> bestRange [t1, t2] ps
    TupleTerm ts ps -> bestRange ts ps
    TypedTerm t _ _ ps -> bestRange [t] ps
    QuantifiedTerm _ _ t ps -> bestRange [t] ps
    LambdaTerm _ _ t ps -> bestRange [t] ps
    CaseTerm t _ ps -> bestRange [t] ps
    LetTerm _ _ t ps -> bestRange [t] ps
    TermToken t -> tokPos t
    MixTypeTerm _ t ps -> bestRange [t] ps
    MixfixTerm ts -> getRange ts
    BracketTerm _ ts ps -> bestRange ts ps
    AsPattern v _ ps -> bestRange [v] ps

instance GetRange TypePattern where
  getRange pat = case pat of
    TypePattern t _ ps -> bestRange [t] ps
    TypePatternToken t -> tokPos t
    MixfixTypePattern ts -> getRange ts
    BracketTypePattern _ ts ps -> bestRange ts ps
    TypePatternArg (TypeArg t _ _ _ _ _ _) ps -> bestRange [t] ps

instance GetRange VarDecl where
    getRange (VarDecl v _ _ p) = bestRange [v] p

instance GetRange TypeArg where
    getRange (TypeArg v _ _ _ _ _ p) = bestRange [v] p

instance GetRange TypeScheme where
    getRange (TypeScheme args t ps) = bestRange args $ bestRange [t] ps

instance GetRange BasicSpec

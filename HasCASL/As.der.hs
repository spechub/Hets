{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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
import HasCASL.HToken

-- * abstract syntax entities with small utility functions
{-! global: UpPos !-}

-- | annotated basic items
data BasicSpec = BasicSpec [Annoted BasicItem]
                  deriving Show

-- | the possible items
data BasicItem = SigItems SigItems
               | ProgItems [Annoted ProgEq] Range
               -- pos "program", dots
               | ClassItems Instance [Annoted ClassItem] Range
               -- pos "class", ";"s
               | GenVarItems [GenVarDecl] Range
               -- pos "var", ";"s
               | FreeDatatype [Annoted DatatypeDecl] Range
               -- pos "free", "type", ";"s
               | GenItems [Annoted SigItems] Range 
               -- pos "generated" "{", ";"s, "}"
               -- or "generated" "type" ";"s
               | AxiomItems [GenVarDecl] [Annoted Term] Range
               -- pos "forall" (if GenVarDecl not empty), dots 
               | Internal [Annoted BasicItem] Range
               -- pos "internal" "{", ";"s, "}"
                 deriving Show

-- | signature items are types or functions
data SigItems = TypeItems Instance [Annoted TypeItem] Range -- including sort
              -- pos "type", ";"s
              | OpItems OpBrand [Annoted OpItem] Range
              -- pos "op", ";"s
                 deriving Show

-- | indicator for predicate, operation or function
data OpBrand = Pred | Op | Fun deriving (Eq, Ord) 

instance Show OpBrand where
    show b = case b of
        Pred -> predS
        Op -> opS
        Fun -> functS

-- | test if the function was declared as predicate
isPred :: OpBrand -> Bool
isPred b = case b of Pred -> True
                     _ -> False

-- | indicator in 'ClassItems' and 'TypeItems'
data Instance = Instance | Plain

instance Show Instance where
    show i = case i of
        Instance -> instanceS
        Plain -> ""

-- | a class item
data ClassItem = ClassItem ClassDecl [Annoted BasicItem] Range 
                 -- pos "{", ";"s "}"
                 deriving Show

-- | declaring class identifiers
data ClassDecl = ClassDecl [ClassId] Kind Range
               -- pos ","s
                 deriving Show

-- | co- or contra- variance indicator                          
data Variance = CoVar | ContraVar deriving (Eq, Ord)

instance Show Variance where
    show v = case v of 
        CoVar -> plusS
        ContraVar -> minusS

-- | (higher) kind or an extended kind (with a variance)
data Kind = ClassKind ClassId           -- ^ plus the declared kind
          | FunKind Kind Kind Range     -- ^ only argument may be an 'ExtKind' 
            -- pos "->" 
          | ExtKind Kind Variance Range  
             -- pos "+" or "-" 
            deriving Show

-- | the string for the universe type
typeUniverseS :: String 
typeUniverseS = "Type"

-- | the type universe
star :: Kind
star = ClassKind $ simpleIdToId $ mkSimpleId typeUniverseS

-- | the 'ExtKind' 'star' 'CoVar' (Type+)
starPlus :: Kind
starPlus = ExtKind star CoVar nullRange

-- | the 'Kind' of the function type
funKind :: Kind
funKind = FunKind (ExtKind star ContraVar nullRange)
             (FunKind starPlus star nullRange) nullRange

-- | construct higher order kind from arguments and result kind
mkFunKind :: [Kind] -> Kind -> Kind
mkFunKind args res = foldr ( \ a k -> FunKind a k nullRange) res args 

-- | the 'Kind' of the product type
prodKind :: Int -> Kind
prodKind n = if n > 1 then mkFunKind (replicate n starPlus) star
             else error "prodKind"

-- | the possible type items 
data TypeItem  = TypeDecl [TypePattern] Kind Range
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
                 deriving Show

-- | a tuple pattern for 'SubtypeDefn' 
data Vars = Var Var | VarTuple [Vars] Range deriving Show

-- | the lhs of most type items 
data TypePattern = TypePattern TypeId [TypeArg] Range
                 -- pos "("s, ")"s 
                 | TypePatternToken Token
                 | MixfixTypePattern [TypePattern]
                 | BracketTypePattern BracketKind [TypePattern] Range
                 -- pos brackets (no parenthesis)
                 | TypePatternArg TypeArg Range
                 -- pos "(", ")"
                   deriving Show

-- | a type synonym for raw kinds (just for readability)
type RawKind = Kind

-- | types based on variable or constructor names and applications
data Type = TypeName TypeId RawKind Int  
          -- Int == 0 means constructor, negative are bound variables
          | TypeAppl Type Type
          | ExpandedType Type Type    -- an alias type with its expansion
          -- only the following variants are parsed
          | KindedType Type Kind Range
          -- pos ":"
          | TypeToken Token
          | BracketType BracketKind [Type] Range
          -- pos "," (between type arguments)
          | MixfixType [Type] 
          -- the following variants should be converted to type applications
          | LazyType Type Range
          -- pos "?"
          | ProductType [Type] Range
          -- pos crosses 
          | FunType Type Arrow Type Range
          -- pos arrow
            deriving Show

-- | a type name with a star kind
mkTypeName :: Id -> Type
mkTypeName i = TypeName i star 0

-- | through away the user's type alias
unalias :: Type -> Type
unalias ty = case ty of 
    ExpandedType _ t -> unalias t 
    _ -> ty

-- | construct a product type
mkProductType :: [Type] -> Range -> Type
mkProductType ts ps = case ts of
    [] -> unitType
    [t] -> t
    _ -> ProductType ts ps

-- | the builtin function arrows
data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Eq, Ord)

instance Show Arrow where
    show a = case a of 
        FunArr -> funS
        PFunArr -> pFun
        ContFunArr -> contFun
        PContFunArr -> pContFun 

-- | construct an infix identifier for a function arrow
arrowId :: Arrow -> Id
arrowId a = mkId $ map mkSimpleId [place, show a, place]

-- | construct a mixfix product identifier with n places 
productId :: Int -> Id
productId n = if n > 1 then
  mkId $ map mkSimpleId $ place : concat (replicate (n-1) [prodS, place])
  else error "productId"

{- | a type with bound type variables. The bound variables within the
scheme should have negative numbers in the order given by the type
argument list. The type arguments store proper kinds (including
downsets) whereas the kind within the type names are only raw
kinds. -}
data TypeScheme = TypeScheme [TypeArg] Type Range
                -- pos "forall", ";"s,  dot (singleton list)
                -- pos "\" "("s, ")"s, dot for type aliases
                  deriving Show

-- | convert a type with unbound variables to a scheme
simpleTypeScheme :: Type -> TypeScheme
simpleTypeScheme t = TypeScheme [] t nullRange

-- | the name for the Unit (or empty product) type 
unitTypeS :: String
unitTypeS = "Unit"

-- | the identifier for the Unit type
unitTypeId :: Id
unitTypeId = simpleIdToId $ mkSimpleId unitTypeS

-- | the Unit type (name)
unitType :: Type 
unitType = TypeName unitTypeId star 0

-- | add an additional Unit type argument to a type 
liftType :: Type -> Range -> Type
liftType t qs = FunType unitType PFunArr t qs

{- | add the Unit type as result type or convert a parsed empty tuple
   to the unit type -}
predType :: Type -> Type
predType t = case t of
                    BracketType Parens [] _ -> unitType
                    _ -> FunType t PFunArr unitType nullRange

-- | change the type within a scheme
mapTypeOfScheme :: (Type -> Type) -> TypeScheme -> TypeScheme
mapTypeOfScheme f (TypeScheme args t ps) =
    TypeScheme args (f t) ps

-- | change the type of the scheme to a 'predType'
predTypeScheme :: TypeScheme -> TypeScheme
predTypeScheme = mapTypeOfScheme predType

-- | indicator for partial or total functions
data Partiality = Partial | Total deriving (Eq, Ord)

instance Show Partiality where
    show p = case p of
        Partial -> quMark
        Total -> exMark

-- | function declarations or definitions
data OpItem = OpDecl [OpId] TypeScheme [OpAttr] Range
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpId [[VarDecl]] TypeScheme Partiality Term Range
               -- pos "("s, ";"s, ")"s, ":" or ":?", "="
              deriving Show

-- | attributes without arguments for binary functions 
data BinOpAttr = Assoc | Comm | Idem deriving Eq

instance Show BinOpAttr where
    show a = case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

-- | possible function attributes (including a term as a unit element)
data OpAttr = BinOpAttr BinOpAttr Range 
            | UnitOpAttr Term Range deriving Show

-- | a polymorphic data type declaration with a deriving clause
data DatatypeDecl = DatatypeDecl 
                    TypePattern 
                    Kind
                    [Annoted Alternative] 
                    [ClassId]
                    Range 
                     -- pos "::=", "|"s, "deriving"
                     deriving Show

{- | Alternatives are subtypes or a constructor with a list of
(curried) tuples as arguments. Only the components of the first tuple
can be addressed by the places of the mixfix constructor. -}
data Alternative = Constructor UninstOpId [[Component]] Partiality Range
                   -- pos: "("s, ";"s, ")"s, "?"
                 | Subtype [Type] Range
                   -- pos: "type", ","s
                   deriving Show

{- | A component is a type with on optional (only pre- or postfix) 
   selector function. -}
data Component = Selector UninstOpId Partiality Type SeparatorKind Range 
                -- pos ",", ":" or ":?"
                | NoSelector Type
                  deriving Show

-- | the possible quantifiers
data Quantifier = Universal | Existential | Unique
                  deriving (Eq, Ord)

instance Show Quantifier where
    show q = case q of
        Universal -> forallS
        Existential -> existsS 
        Unique -> existsS ++ exMark

-- | the possibly type annotations of terms
data TypeQual = OfType | AsType | InType | Inferred deriving (Eq, Ord)

instance Show TypeQual where
    show q = case q of
        OfType -> colonS
        AsType -> asS
        InType -> inS
        Inferred -> colonS

-- | an indicator of (otherwise equivalent) let or where equations
data LetBrand = Let | Where | Program deriving (Show, Eq, Ord)

-- | the possible kinds of brackets (that should match when parsed) 
data BracketKind = Parens | Squares | Braces deriving (Show, Eq, Ord)

-- | the brackets as strings for printing
getBrackets :: BracketKind -> (String, String)
getBrackets b = case b of
                       Parens -> ("(", ")")
                       Squares -> ("[", "]")
                       Braces -> ("{", "}")

-- | the brackets as tokens with positions
mkBracketToken :: BracketKind -> Range -> [Token]
mkBracketToken k ps = 
       map ( \ s -> Token s ps) $ (\ (o,c) -> [o,c]) $ getBrackets k

{- | The possible terms and patterns. Formulas are also kept as terms. Local variables and constants are kept separatetly. The variant 'ResolvedMixTerm' is an intermediate representation for type checking only. -}
data Term = QualVar VarDecl
          -- pos "(", "var", ":", ")"
          | QualOp OpBrand InstOpId TypeScheme Range
          -- pos "(", "op", ":", ")" 
          | ApplTerm Term Term Range  -- analysed
          -- pos?
          | TupleTerm [Term] Range    -- special application
          -- pos "(", ","s, ")"
          | TypedTerm Term TypeQual Type Range
          -- pos ":", "as" or "in"
          | AsPattern VarDecl Pattern Range          
          -- pos "@"
          | QuantifiedTerm Quantifier [GenVarDecl] Term Range
          -- pos quantifier, ";"s, dot
          -- only "forall" may have a TypeVarDecl
          | LambdaTerm [Pattern] Partiality Term Range
          -- pos "\", dot (plus "!") 
          | CaseTerm Term [ProgEq] Range
          -- pos "case", "of", "|"s 
          | LetTerm LetBrand [ProgEq] Term Range
          -- pos "where", ";"s
          | ResolvedMixTerm Id [Term] Range
          | TermToken Token
          | MixTypeTerm TypeQual Type Range
          | MixfixTerm [Term]
          | BracketTerm BracketKind [Term] Range
          -- pos brackets, ","s 
            deriving (Show, Eq, Ord)

-- | patterns are terms constructed by the first six variants
type Pattern = Term

-- | construct a tuple from non-singleton lists
mkTupleTerm :: [Term] -> Range -> Term
mkTupleTerm ts ps = if isSingle ts then head ts else TupleTerm ts ps

-- | an equation or a case as pair of a pattern and a term 
data ProgEq = ProgEq Pattern Term Range deriving (Show, Eq, Ord)
            -- pos "=" (or "->" following case-of)


{- | an indicator if variables were separated by commas or by separate
declarations -}
data SeparatorKind = Comma | Other deriving Show

-- | a variable with its type
data VarDecl = VarDecl Var Type SeparatorKind Range deriving Show
               -- pos "," or ":" 

-- | the kind of a type variable (or a type argument in schemes) 
data VarKind = VarKind Kind | Downset Type | MissingKind 
               deriving (Show, Eq, Ord)

-- | a (simple) type variable with its kind (or supertype)
data TypeArg = TypeArg TypeId VarKind RawKind Int SeparatorKind Range
               -- pos "," or ":" ("+" or "-" pos is moved to ExtClass)
               deriving Show

-- | a value or type variable
data GenVarDecl = GenVarDecl VarDecl
                | GenTypeVarDecl TypeArg
                  deriving (Show, Eq, Ord)

-- | a polymorphic function identifier with type arguments 
data OpId = OpId UninstOpId [TypeArg] Range deriving (Show, Eq, Ord)
     -- pos "[", ";"s, "]" 

-- | an instantiated function identifiers 
data InstOpId = InstOpId UninstOpId [Type] Range deriving (Show, Eq, Ord)

-- * synonyms for identifiers

{- | type variable are expected to be simple whereas type constructors may be 
     mixfix- and compound identifiers -} 
type TypeId = Id
type UninstOpId = Id

{- | variables are non-compound identifiers but may be mixfix if their
types permit -}
type Var = Id

-- | class identifier are simple but may be compound (like CASL sorts)
type ClassId = Id

-- * symbol data types
-- | symbols 
data SymbItems = SymbItems SymbKind [Symb] [Annotation] Range 
                  -- pos: kind, commas
                  deriving (Show, Eq)

-- | mapped symbols 
data SymbMapItems = SymbMapItems SymbKind [SymbOrMap] [Annotation] Range
                      -- pos: kind commas
                      deriving (Show, Eq)

-- | kind of symbols
data SymbKind = Implicit | SK_type | SK_sort | SK_fun | SK_op | SK_pred 
              | SK_class
                 deriving (Show, Eq, Ord)

-- | type annotated symbols
data Symb = Symb Id (Maybe SymbType) Range 
            -- pos: colon (or empty)
            deriving (Show, Eq)

-- | type for symbols
data SymbType = SymbType TypeScheme
            deriving (Show, Eq)

-- | mapped symbol
data SymbOrMap = SymbOrMap Symb (Maybe Symb) Range
                   -- pos: "|->" (or empty)
                   deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- equality instances ignoring positions
-- ----------------------------------------------------------------------------

instance Eq Kind where
    ClassKind i1 == ClassKind i2 = i1 == i2
    FunKind p1 c1 _ == FunKind p2 c2 _ = (p1, c1) == (p2, c2)
    ExtKind c1 v1 _ == ExtKind c2 v2 _ = (c1, v1) == (c2, v2)
    _ == _ = False

instance Ord Kind where
    ClassKind i1 <= ClassKind i2 = i1 <= i2
    FunKind p1 c1 _ <= FunKind p2 c2 _ = (p1, c1) <= (p2, c2)
    ExtKind c1 v1 _ <= ExtKind c2 v2 _ = (c1, v1) <= (c2, v2)
    ClassKind _ <= _ = True
    _ <= ClassKind _ = False
    ExtKind _ _ _ <= _ = True
    _ <= ExtKind _ _ _ = False

instance Eq Type where 
    TypeName i1 k1 v1 == TypeName i2 k2 v2 = 
        if v1 == 0 && v2 == 0 then (i1, k1) == (i2, k2)
        else (v1, k1) == (v2, k2)
    TypeAppl f1 a1 == TypeAppl f2 a2 = (f1, a1) == (f2, a2)
    TypeToken t1 == TypeToken t2 = t1 == t2
    BracketType b1 l1 _ == BracketType b2 l2 _ = (b1, l1) == (b2, l2)
    KindedType t1 k1 _ == KindedType t2 k2 _ = (t1, k1) == (t2, k2)
    MixfixType l1 == MixfixType l2 = l1 == l2
    LazyType t1 _ == LazyType t2 _ = t1 == t2 
    ProductType l1 _ == ProductType l2 _ = l1 == l2
    FunType f1 a1 g1 _ == FunType f2 a2 g2 _ = (f1, a1, g1) == (f2, a2, g2)
    ExpandedType _ t1 == t2 = t1 == t2
    t1 == ExpandedType _ t2 = t1 == t2
    _ == _ = False

instance Ord Type where
    TypeName i1 k1 v1 <= TypeName i2 k2 v2 = 
        if v1 == 0 && v2 == 0 then (i1, k1) <= (i2, k2)
        else (v1, k1) <= (v2, k2)
    TypeAppl f1 a1 <= TypeAppl f2 a2 = (f1, a1) <= (f2, a2)
    TypeToken t1 <= TypeToken t2 = t1 <= t2
    BracketType b1 l1 _ <= BracketType b2 l2 _ = (b1, l1) <= (b2, l2)
    KindedType t1 k1 _ <= KindedType t2 k2 _ = (t1, k1) <= (t2, k2)
    MixfixType l1 <= MixfixType l2 = l1 <= l2
    LazyType t1 _ <= LazyType t2 _ = t1 <= t2 
    ProductType l1 _ <= ProductType l2 _ = l1 <= l2
    FunType f1 a1 g1 _ <= FunType f2 a2 g2 _ = (f1, a1, g1) <= (f2, a2, g2)
    ExpandedType _ t1 <= t2 = t1 <= t2
    t1 <= ExpandedType _ t2 = t1 <= t2
    TypeName _ _ _ <= _ = True
    _ <= TypeName _ _ _ = False
    TypeAppl _ _ <= _ = True 
    _ <= TypeAppl _ _ = False
    TypeToken _ <= _ = True
    _ <= TypeToken _ = False
    BracketType _ _ _ <= _ = True
    _ <= BracketType _ _ _ = False
    KindedType _ _ _ <= _ = True
    _ <= KindedType _ _ _ = False
    MixfixType _ <= _ = True
    _ <= MixfixType _ = False
    LazyType _ _<= _ = True
    _ <= LazyType _ _ = False
    ProductType _ _<= _ = True
    _ <= ProductType _ _ = False

-- is this equality only needed for the equality of schemes? 
instance Eq TypeArg where
    TypeArg i1 k1 _ _ _ _ == TypeArg i2 k2 _ _ _ _ = (i1, k1) == (i2, k2)
instance Ord TypeArg where
    TypeArg i1 k1 _ _ _ _ <= TypeArg i2 k2 _ _ _ _ = (i1, k1) <= (i2, k2)

-- when are analyzed schemes equal? The name of variables should not matter
instance Eq TypeScheme where
    TypeScheme v1 t1 _ == TypeScheme v2 t2 _ = (v1, t1) == (v2, t2) 
instance Ord TypeScheme where
    TypeScheme v1 t1 _ <= TypeScheme v2 t2 _ = (v1, t1) <= (v2, t2) 

instance Eq Vars where
    Var v1 == Var v2 = v1 == v2
    VarTuple l1 _ == VarTuple l2 _ = l1 == l2
    _ == _ = False

instance Eq VarDecl where
    VarDecl v1 t1 _ _ == VarDecl v2 t2 _ _ = (v1, t1) == (v2, t2) 
instance Ord VarDecl where
    VarDecl v1 t1 _ _ <= VarDecl v2 t2 _ _ = (v1, t1) <= (v2, t2) 

instance Eq OpAttr where 
    BinOpAttr b1 _ == BinOpAttr b2 _ = b1 == b2
    UnitOpAttr t1 _ == UnitOpAttr t2 _= t1 == t2
    _ == _ = False

instance Eq Alternative where 
    Constructor i1 l1 p1 _ == Constructor i2 l2 p2 _ =
        (i1, l1, p1) == (i2, l2, p2)
    Subtype t1 _ == Subtype t2 _ = t1 == t2
    _ == _ = False

instance Eq Component where 
    Selector i1 p1 t1 _ _ == Selector i2 p2 t2 _ _ =
        (i1, t1, p1) == (i2, t2, p2)
    NoSelector t1 == NoSelector t2 = t1 == t2
    _ == _ = False

{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable

   
   abstract syntax for HasCASL
   more liberal than Concrete-Syntax.txt
   annotations are almost as for CASL

-}

module HasCASL.As where

import Common.Id
import Common.Keywords
import Common.AS_Annotation 
import HasCASL.HToken

-- * abstract syntax entities 

data BasicSpec = BasicSpec [Annoted BasicItem]
                  deriving (Show, Eq)

data BasicItem = SigItems SigItems
               | ProgItems [Annoted ProgEq] [Pos]
               -- pos "program", dots
               | ClassItems Instance [Annoted ClassItem] [Pos]
               -- pos "class", ";"s
               | GenVarItems [GenVarDecl] [Pos]
               -- pos "var", ";"s
               | FreeDatatype [Annoted DatatypeDecl] [Pos]
               -- pos "free", "type", ";"s
               | GenItems [Annoted SigItems] [Pos] 
               -- pos "generated" "{", ";"s, "}"
               -- or "generated" "type" ";"s
               | AxiomItems [GenVarDecl] [Annoted Term] [Pos]
               -- pos "forall" (if GenVarDecl not empty), dots 
               | Internal [Annoted BasicItem] [Pos]
               -- pos "internal" "{", ";"s, "}"
                 deriving (Show, Eq)

data SigItems = TypeItems Instance [Annoted TypeItem] [Pos] -- including sort
              -- pos "type", ";"s
              | OpItems OpBrand [Annoted OpItem] [Pos]
              -- pos "op", ";"s
                 deriving (Show, Eq)

-- | indicator for predicate, operation or function
data OpBrand = Pred | Op | Fun deriving (Eq, Ord) 

instance Show OpBrand where
    show b = case b of
        Pred -> predS
        Op -> opS
        Fun -> functS

isPred :: OpBrand -> Bool
isPred b = case b of Pred -> True
		     _ -> False

-- | indicator in 'ClassItems' and 'TypeItems'
data Instance = Instance | Plain deriving Eq

instance Show Instance where
    show i = case i of
        Instance -> instanceS
        Plain -> ""

data ClassItem = ClassItem ClassDecl [Annoted BasicItem] [Pos] 
                 -- pos "{", ";"s "}"
                 deriving (Show, Eq)

data ClassDecl = ClassDecl [ClassId] Kind [Pos]
               -- pos ","s
                 deriving (Show, Eq)
                          
data Variance = CoVar | ContraVar deriving (Eq, Ord)

instance Show Variance where
    show v = case v of 
        CoVar -> plusS
	ContraVar -> minusS

-- | kind or an extended kind
data Kind = MissingKind -- ^ initially missing information
          | Downset (Maybe Token) Type Kind [Pos] -- ^ plus the derived kind
          | ClassKind ClassId Kind                -- ^ plus the declared kind
          | Intersection [Kind] [Pos]   -- ^ with equal raw kinds
          | FunKind Kind Kind [Pos]     -- ^ only argument may be an 'ExtKind' 
            -- pos "->" 
          | ExtKind Kind Variance [Pos] -- ^ no 'InVar'  
             -- pos "+" or "-" 
            deriving Show

-- | the type universe
star :: Kind
star = Intersection [] []

-- | the 'ExtKind' 'star' 'CoVar' (Type+)
starPlus :: Kind
starPlus = ExtKind star CoVar []

-- | the 'Kind' of the function type
funKind :: Kind
funKind = FunKind (ExtKind star ContraVar [])
             (FunKind starPlus star []) []

-- | the 'Kind' of the pair product type
prodKind :: Kind
prodKind = FunKind starPlus (FunKind starPlus star []) []

data TypeItem  = TypeDecl [TypePattern] Kind [Pos]
               -- pos ","s
               | SubtypeDecl [TypePattern] Type [Pos]
               -- pos ","s, "<"
               | IsoDecl [TypePattern] [Pos]
               -- pos "="s
               | SubtypeDefn TypePattern Vars Type (Annoted Term) [Pos]
               -- pos "=", "{", ":", dot, "}"
               | AliasType TypePattern (Maybe Kind) TypeScheme [Pos]
               -- pos ":="
               | Datatype DatatypeDecl
                 deriving (Show, Eq)

-- | a tuple pattern for 'SubtypeDefn' 
data Vars = Var Var | VarTuple [Vars] [Pos] deriving Show

data TypePattern = TypePattern TypeId [TypeArg] [Pos]
                 -- pos "("s, ")"s 
                 | TypePatternToken Token
                 | MixfixTypePattern [TypePattern]
                 | BracketTypePattern BracketKind [TypePattern] [Pos]
                 -- pos brackets (no parenthesis)
                 | TypePatternArg TypeArg [Pos]
                 -- pos "(", ")"
                   deriving (Show, Eq)

data Type = TypeName TypeId Kind Int  -- (Int == 0 means constructor,
				      -- negative are bound variables)
          | TypeAppl Type Type
          | ExpandedType Type Type
          | TypeToken Token
          | BracketType BracketKind [Type] [Pos]
          -- pos "," (between type arguments)
          | KindedType Type Kind [Pos]
          -- pos ":"
          | MixfixType [Type] 
          | LazyType Type [Pos]
          -- pos "?"
          | ProductType [Type] [Pos]
          -- pos crosses 
          | FunType Type Arrow Type [Pos]
          -- pos arrow
            deriving (Show)

unalias :: Type -> Type
unalias ty = case ty of 
    ExpandedType _ t -> unalias t 
    _ -> ty

mkProductType :: [Type] -> [Pos] -> Type
mkProductType ts ps = if isSingle ts then head ts else ProductType ts ps

data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Eq, Ord)

instance Show Arrow where
    show a = case a of 
        FunArr -> funS
        PFunArr -> pFun
        ContFunArr -> contFun
        PContFunArr -> pContFun 

arrowId :: Arrow -> Id
arrowId a = Id (map mkSimpleId [place, show a, place]) [] []

productId :: Id
productId = Id (map mkSimpleId [place, prodS, place]) [] []

-- no curried notation for bound variables 
data TypeScheme = TypeScheme [TypeArg] Type [Pos]
                -- pos "forall", ";"s,  dot (singleton list)
                -- pos "\" "("s, ")"s, dot for type aliases
                  deriving (Show, Ord)

simpleTypeScheme :: Type -> TypeScheme
simpleTypeScheme t = TypeScheme [] t []

logicalType :: Type 
logicalType = -- TypeName (simpleIdToId (mkSimpleId "Unit")) star 0
              ProductType [] [] 

mapTypeOfScheme :: (Type -> Type) -> TypeScheme -> TypeScheme
mapTypeOfScheme f (TypeScheme args t ps) =
    TypeScheme args (f t) ps

predTypeScheme :: TypeScheme -> TypeScheme
predTypeScheme = mapTypeOfScheme predType

predType :: Type -> Type
predType t = case t of
                    BracketType Parens [] _ -> logicalType
                    _ -> FunType t PFunArr logicalType []

data Partiality = Partial | Total deriving (Eq, Ord)

instance Show Partiality where
    show p = case p of
        Partial -> quMark
        Total -> exMark

data OpItem = OpDecl [OpId] TypeScheme [OpAttr] [Pos]
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpId [[VarDecl]] TypeScheme Partiality Term [Pos]
               -- pos "("s, ";"s, ")"s, ":" or ":?", "="
              deriving (Show, Eq)

data BinOpAttr = Assoc | Comm | Idem deriving Eq

instance Show BinOpAttr where
    show a = case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS


data OpAttr = BinOpAttr BinOpAttr [Pos] 
            | UnitOpAttr Term [Pos] deriving (Show)

data DatatypeDecl = DatatypeDecl 
                    TypePattern 
                    Kind
                    [Annoted Alternative] 
                    [ClassId]
                    [Pos] 
                     -- pos "::=", "|"s, "deriving"
                     deriving (Show, Eq)

data Alternative = Constructor UninstOpId [[Component]] Partiality [Pos]
                   -- pos: "("s, ";"s, ")"s, "?"
                 | Subtype [Type] [Pos]
                   -- pos: "type", ","s
                   deriving (Show)

data Component = Selector UninstOpId Partiality Type SeparatorKind Pos 
                -- pos ",", ":" or ":?"
                | NoSelector Type
                  deriving (Show)

data Quantifier = Universal | Existential | Unique
                  deriving (Eq, Ord)

instance Show Quantifier where
    show q = case q of
        Universal -> forallS
        Existential -> existsS 
        Unique -> existsS ++ exMark

data TypeQual = OfType | AsType | InType deriving (Eq, Ord)

instance Show TypeQual where
    show q = case q of
        OfType -> colonS
        AsType -> asS
        InType -> inS

data LetBrand = Let | Where deriving (Show, Eq, Ord)

data BracketKind = Parens | Squares | Braces deriving (Show, Eq, Ord)

getBrackets :: BracketKind -> (String, String)
getBrackets b = case b of
                       Parens -> ("(", ")")
                       Squares -> ("[", "]")
                       Braces -> ("{", "}")

-- parse quantified formulae as terms first
-- eases also parsing of formulae in parenthesis

data Term = QualVar VarDecl
          -- pos "(", "var", ":", ")"
          | QualOp OpBrand InstOpId TypeScheme [Pos]
          -- pos "(", "op", ":", ")" 
          | ResolvedMixTerm Id [Term] [Pos]
          | ApplTerm Term Term [Pos]  -- analysed
          -- pos?
          | TupleTerm [Term] [Pos]
          -- pos "(", ","s, ")"
          | TypedTerm Term TypeQual Type [Pos]
          -- pos ":", "as" or "in"
          | QuantifiedTerm Quantifier [GenVarDecl] Term [Pos]
          -- pos quantifier, ";"s, dot
          -- only "forall" may have a TypeVarDecl
          | LambdaTerm [Pattern] Partiality Term [Pos]
          -- pos "\", dot (plus "!") 
          | CaseTerm Term [ProgEq] [Pos]
          -- pos "case", "of", "|"s 
          | LetTerm LetBrand [ProgEq] Term [Pos]
          -- pos "where", ";"s
          | TermToken Token
          | MixTypeTerm TypeQual Type [Pos]
          | MixfixTerm [Term]
          | BracketTerm BracketKind [Term] [Pos]
          -- pos brackets, ","s 
          | AsPattern VarDecl Pattern [Pos]          
          -- pos "@"
            deriving (Show,Ord)

type Pattern = Term

mkTupleTerm :: [Term] -> [Pos] -> Term
mkTupleTerm ts ps = if isSingle ts then head ts else TupleTerm ts ps

data ProgEq = ProgEq Pattern Term Pos deriving (Show, Ord)
            -- pos "=" (or "->" following case-of)
-- ----------------------------------------------------------------------------
-- (type) var decls
-- ----------------------------------------------------------------------------

data SeparatorKind = Comma | Other deriving (Show, Eq, Ord)

data VarDecl = VarDecl Var Type SeparatorKind [Pos] deriving (Show, Ord)
               -- pos "," or ":" 

data TypeArg = TypeArg TypeId Kind SeparatorKind [Pos]
               -- pos "," or ":" ("+" or "-" pos is moved to ExtClass)
               deriving (Show)

instance Ord TypeArg where
    TypeArg v1 _ _ _ <= TypeArg v2 _ _ _
        = v1 <= v2

data GenVarDecl = GenVarDecl VarDecl
                | GenTypeVarDecl TypeArg
                  deriving (Show, Eq, Ord)

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpId = OpId UninstOpId [TypeArg] [Pos] deriving (Show, Eq, Ord)
     -- pos "[", ";"s, "]" 
data InstOpId = InstOpId UninstOpId [Type] [Pos] deriving (Show, Eq, Ord)

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeId = Id
type UninstOpId = Id

type Var = Id
type ClassId = Id -- TOKEN-ID (one token with compound list, like CASL sorts)

-- * symbol data types
-- | symbols 
data SymbItems = SymbItems SymbKind [Symb] [Annotation] [Pos] 
		  -- pos: kind, commas
		  deriving (Show, Eq)

-- | mapped symbols 
data SymbMapItems = SymbMapItems SymbKind [SymbOrMap] [Annotation] [Pos]
		      -- pos: kind commas
		      deriving (Show, Eq)

-- | kind of symbols
data SymbKind = Implicit | SK_type | SK_sort | SK_fun | SK_op | SK_pred 
	      | SK_class
		 deriving (Show, Eq, Ord)

-- | type annotated symbols
data Symb = Symb Id (Maybe SymbType) [Pos] 
	    -- pos: colon (or empty)
	    deriving (Show, Eq)

-- | type for symbols
data SymbType = SymbType TypeScheme
	    deriving (Show, Eq)

-- | mapped symbol
data SymbOrMap = SymbOrMap Symb (Maybe Symb) [Pos]
		   -- pos: "|->" (or empty)
		   deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- equality instances while ignoring positions
-- ----------------------------------------------------------------------------

instance Eq Kind where
    MissingKind == MissingKind = True
    Downset _ t1 _ _ == Downset _ t2 _ _ = t1 == t2
    ClassKind i1 _ == ClassKind i2 _ = i1 == i2
    Intersection ks1 _ == Intersection ks2 _ = ks1 == ks2
    FunKind p1 c1 _ == FunKind p2 c2 _ = (p1, c1) == (p2, c2)
    ExtKind c1 v1 _ == ExtKind c2 v2 _ = (c1, v1) == (c2, v2)
    _ == _ = False

instance Ord Kind where
    MissingKind <= MissingKind = True
    Downset _ t1 _ _ <= Downset _ t2 _ _ = t1 <= t2
    ClassKind i1 _ <= ClassKind i2 _ = i1 <= i2
    Intersection ks1 _ <= Intersection ks2 _ = ks1 <= ks2
    FunKind p1 c1 _ <= FunKind p2 c2 _ = (p1, c1) <= (p2, c2)
    ExtKind c1 v1 _ <= ExtKind c2 v2 _ = (c1, v1) <= (c2, v2)
    MissingKind <= _ = True
    _ <= MissingKind = False
    Downset _ _ _ _ <= _ = True
    _ <= Downset _ _ _ _ = False
    ClassKind _ _ <= _ = True
    _ <= ClassKind _ _ = False
    Intersection _ _ <= _ = True
    _ <= Intersection _ _ = False
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

instance Eq TypeArg where
    TypeArg i1 k1 _ _ == TypeArg i2 k2 _ _ = (i1, k1) == (i2, k2)

-- this is strict syntactic equality
-- unification only captures analysed types and ignores lazy types! 
instance Eq TypeScheme where
    TypeScheme v1 t1 _ == TypeScheme v2 t2 _ = (v1, t1) == (v2, t2) 

instance Eq Vars where
    Var v1 == Var v2 = v1 == v2
    VarTuple l1 _ == VarTuple l2 _ = l1 == l2
    _ == _ = False

instance Eq VarDecl where
    VarDecl v1 t1 _ _ == VarDecl v2 t2 _ _ = (v1, t1) == (v2, t2) 

instance Eq Term where
    QualVar v1 == QualVar v2 = v1 == v2
    QualOp b1 i1 s1 _ == QualOp b2 i2 s2 _ = (b1, i1, s1) == (b2, i2, s2) 
    ResolvedMixTerm i1 t1 _ == ResolvedMixTerm i2 t2 _ = (i1, t1) == (i2, t2) 
    ApplTerm s1 t1 _ == ApplTerm s2 t2 _ = (s1, t1) == (s2, t2) 
    TupleTerm l1 _ == TupleTerm l2 _ = l1 == l2
    TypedTerm s1 q1 t1 _ == TypedTerm s2 q2 t2 _ = (q1, t1, s1) == (q2, t2, s2)
    QuantifiedTerm q1 v1 t1 _ == QuantifiedTerm q2 v2 t2 _ =
        (q1, v1, t1) == (q2, v2, t2)
    LambdaTerm v1 p1 t1 _ == LambdaTerm v2 p2 t2 _ = 
        (p1, v1, t1) == (p2, v2, t2)
    CaseTerm t1 e1 _ ==  CaseTerm t2 e2 _ = (t1, e1) == (t2, e2)
    LetTerm b1 e1 t1 _ == LetTerm b2 e2 t2 _  = (b1, t1, e1) == (b2, t2, e2)
    TermToken t1 == TermToken t2 = t1 == t2
    MixTypeTerm q1 t1 _ == MixTypeTerm q2 t2 _ = (q1, t1) == (q2, t2)
    MixfixTerm l1 == MixfixTerm l2 = l1 == l2
    BracketTerm b1 l1 _ == BracketTerm b2 l2 _ = (b1, l1) == (b2, l2) 
    _ == _ = False

instance Eq ProgEq where
   ProgEq p1 t1 _ == ProgEq p2 t2 _ = (p1, t1) == (p2, t2) 

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

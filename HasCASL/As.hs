
{- HetCATS/HasCASL/As.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   abstract syntax for HasCASL
   more liberal than HetCATS/HasCASL/Concrete-Syntax.txt
   annotations almost as in HetCATS/CASL/AS_Basic_CASL.hs v 1.8 
-}

module HasCASL.As where

import Common.Id
import Common.AS_Annotation 
import Common.Lib.Set

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
                 deriving (Show, Eq)

data SigItems = TypeItems Instance [Annoted TypeItem] [Pos] -- including sort
              -- pos "type", ";"s
              | OpItems [Annoted OpItem] [Pos]
              -- pos "op", ";"s
                 deriving (Show, Eq)

-- "instance" indicator
data Instance = Instance | Plain deriving (Show, Eq)

data ClassItem = ClassItem ClassDecl [Annoted BasicItem] [Pos] 
                 -- pos "{", ";"s "}"
                 deriving (Show, Eq)

data ClassDecl = ClassDecl [ClassId] Kind [Pos]
               -- pos ","s
               | SubclassDecl [ClassId] Kind Class [Pos]
               -- pos ","s, "<"
               | ClassDefn ClassId Kind Class [Pos]
               -- pos "="
               | DownsetDefn ClassId Token Type [Pos] 
	       -- pos " =" "{", dot, "<", typeVar,  "}"
                 deriving (Show, Eq)
                          
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

data Vars = Var Var | VarTuple [Vars] [Pos] deriving (Show, Eq)

data TypePattern = TypePattern TypeId [TypeArg] [Pos]
                 -- pos "("s, ")"s 
                 | TypePatternToken Token
                 | MixfixTypePattern [TypePattern]
                 | BracketTypePattern BracketKind [TypePattern] [Pos]
                 -- pos brackets (no parenthesis)
                 | TypePatternArg TypeArg [Pos]
		 -- pos "(", ")"
                   deriving (Show, Eq)

data Type = TypeName TypeId Kind Int  -- (Int == 0 means constructor)
	  | TypeAppl Type Type
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

data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Show, Eq, Ord)

data Pred = IsIn ClassId [Type]
              deriving (Show, Eq)

data Qual t = [Pred] :=> t
              deriving (Show, Eq)

-- no curried notation for bound variables 
data TypeScheme = TypeScheme [TypeArg] (Qual Type) [Pos]
                -- pos "forall", ";"s,  dot (singleton list)
                -- pos "\" "("s, ")"s, dot for type aliases
                  deriving (Show)

simpleTypeScheme :: Type -> TypeScheme
simpleTypeScheme t = TypeScheme [] ([] :=> t) []

logicalType :: Type 
logicalType = TypeName (simpleIdToId (mkSimpleId "Unit")) star 0
-- or ProductType [] [] 

predTypeScheme :: TypeScheme -> TypeScheme
predTypeScheme (TypeScheme vs (qs :=> t) ps) = 
    TypeScheme vs (qs :=> predType t) ps

predType :: Type -> Type
predType t = FunType t PFunArr logicalType []

data Partiality = Partial | Total deriving (Show, Eq, Ord)

data OpItem = OpDecl [OpId] TypeScheme [OpAttr] [Pos]
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpId [Pattern] TypeScheme Partiality Term [Pos]
               -- pos "("s, ")"s, ":" or ":?", "="
              deriving (Show, Eq)

data BinOpAttr = Assoc | Comm | Idem deriving (Show, Eq, Ord)

data OpAttr = BinOpAttr BinOpAttr [Pos] 
	    | UnitOpAttr Term [Pos] deriving (Show)

data DatatypeDecl = DatatypeDecl 
                    TypePattern 
		    Kind
                    [Annoted Alternative] 
                    (Maybe Class) 
                    [Pos] 
		     -- pos "::=", "|"s, "deriving"
		     deriving (Show, Eq)

data Alternative = Constructor UninstOpId [Components] Partiality [Pos]
		   -- pos: "?"
		 | Subtype [Type] [Pos]
		   -- pos: "type", ","s
		   deriving (Show)

data Components = Selector UninstOpId Partiality Type SeparatorKind Pos 
		-- pos ",", ":" or ":?"
		| NoSelector Type
		| NestedComponents [Components] [Pos]
		  -- pos : "(", ";"s, ")"
		  deriving (Show)

data Quantifier = Universal | Existential | Unique
		  deriving (Show, Eq, Ord)

data TypeQual = OfType | AsType | InType deriving (Show, Eq, Ord)

data BracketKind = Parens | Squares | Braces deriving (Show, Eq, Ord)

getBrackets :: BracketKind -> (String, String)
getBrackets b = case b of
		       Parens -> ("(", ")")
		       Squares -> ("[", "]")
		       Braces -> ("{", "}")

-- parse quantified formulae as terms first
-- eases also parsing of formulae in parenthesis

data Term = QualVar Var Type [Pos]
	  -- pos "(", "var", ":", ")"
	  | QualOp InstOpId TypeScheme [Pos]
	  -- pos "(", "op", ":", ")" 
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
	  | LetTerm [ProgEq] Term [Pos]
	  -- pos "where", ";"s
	  | TermToken Token
          | MixfixTerm [Term]
	  | BracketTerm BracketKind [Term] [Pos]
	  -- pos brackets, ","s 
	    deriving (Show)

data Pattern = PatternVar VarDecl
             -- pos ";"s 
	     | PatternConstr InstOpId TypeScheme [Pattern] [Pos] 
	     -- constructor or toplevel operation applied to arguments
	     -- pos "("s, ")"s
             | PatternToken Token
	     | BracketPattern BracketKind [Pattern] [Pos]
	     -- pos brackets, ","s
	     | TuplePattern [Pattern] [Pos]
	     -- pos ","s
	     | MixfixPattern [Pattern] -- or HO-Pattern
	     | TypedPattern Pattern Type [Pos]	     -- pos ":"  
	     | AsPattern Pattern Pattern [Pos]
	     -- pos "@"
	       deriving (Show)

data ProgEq = ProgEq Pattern Term Pos deriving (Show)
	    -- pos "=" (or "->" following case-of)
-- ----------------------------------------------------------------------------
-- (type) var decls
-- ----------------------------------------------------------------------------

data SeparatorKind = Comma | Other deriving (Show)

data VarDecl = VarDecl Var Type SeparatorKind [Pos] deriving (Show)
	       -- pos "," or ":" 

data TypeArg = TypeArg TypeId Kind SeparatorKind [Pos]
	       -- pos "," or ":" ("+" or "-" pos is moved to ExtClass)
	       deriving (Show)

data GenVarDecl = GenVarDecl VarDecl
		| GenTypeVarDecl TypeArg
		  deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- class
-- ----------------------------------------------------------------------------

data Variance = CoVar | ContraVar | InVar deriving (Show, Eq, Ord)

data Kind = ExtClass Class Variance [Pos]
	     -- pos "+" or "-" 
	    | KindAppl Kind Kind [Pos]
	    -- pos "->" 
	    deriving (Show)

data Class = Downset Type   -- not parsed directly
	   | Intersection { iclass :: Set ClassId, classPos :: [Pos] }  
	   -- pos "(", ","s, ")"
	     deriving (Show)

universe :: Class
universe = Intersection empty []

star :: Kind
star = ExtClass universe InVar []

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpId = OpId UninstOpId [TypeArg] [Pos] deriving (Show, Eq)
     -- pos "[", ";"s, "]" 
data InstOpId = InstOpId UninstOpId [Type] [Pos] deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeId = Id
type UninstOpId = Id

type Var = Id
type ClassId = Id -- TOKEN-ID (one token with compound list, like CASL sorts)

-- ----------------------------------------------------------------------------
-- equality instances while ignoring positions
-- ----------------------------------------------------------------------------

instance Eq Class where
    Intersection i1 _ == Intersection i2 _ = i1 == i2
    Downset t1 == Downset t2 = t1 == t2
    _ == _ = False

instance Eq Kind where
    ExtClass c1 v1 _ == ExtClass c2 v2 _ = (c1, v1) == (c2, v2)
    KindAppl p1 c1 _ == KindAppl p2 c2 _ = (p1, c1) == (p2, c2)
    _ == _ = False

instance Eq Type where 
    TypeName i1 k1 v1 == TypeName i2 k2 v2 = (i1, k1, v1) == (i2, k2, v2)
    TypeAppl f1 a1 == TypeAppl f2 a2 = (f1, a1) == (f2, a2)
    TypeToken t1 == TypeToken t2 = t1 == t2
    BracketType b1 l1 _ == BracketType b2 l2 _ = (b1, l1) == (b2, l2)
    KindedType t1 k1 _ == KindedType t2 k2 _ = (t1, k1) == (t2, k2)
    MixfixType l1 == MixfixType l2 = l1 == l2
    LazyType t1 _ == LazyType t2 _ = t1 == t2 
    ProductType l1 _ == ProductType l2 _ = l1 == l2
    FunType f1 a1 g1 _ == FunType f2 a2 g2 _ = (f1, a1, g1) == (f2, a2, g2)
    _ == _ = False

instance Eq TypeArg where
    TypeArg i1 k1 _ _ == TypeArg i2 k2 _ _ = (i1, k1) == (i2, k2)

-- this is strict syntactic equality
-- unification only captures analysed types and ignores lazy types! 
instance Eq TypeScheme where
    TypeScheme v1 t1 _ == TypeScheme v2 t2 _ = (v1, t1) == (v2, t2) 

instance Eq VarDecl where
    VarDecl v1 t1 _ _ == VarDecl v2 t2 _ _ = (v1, t1) == (v2, t2) 

instance Eq Term where
    QualVar v1 t1 _ == QualVar v2 t2 _ = (v1, t1) == (v2, t2) 
    QualOp i1 s1 _ == QualOp  i2 s2 _ = (i1, s1) == (i2, s2) 
    ApplTerm s1 t1 _ == ApplTerm s2 t2 _ = (s1, t1) == (s2, t2) 
    TupleTerm l1 _ == TupleTerm l2 _ = l1 == l2
    TypedTerm s1 q1 t1 _ == TypedTerm s2 q2 t2 _ = (q1, t1, s1) == (q2, t2, s2)
    QuantifiedTerm q1 v1 t1 _ == QuantifiedTerm q2 v2 t2 _ =
	(q1, v1, t1) == (q2, v2, t2)
    LambdaTerm v1 p1 t1 _ == LambdaTerm v2 p2 t2 _ = 
	(p1, v1, t1) == (p2, v2, t2)
    CaseTerm t1 e1 _ ==  CaseTerm t2 e2 _ = (t1, e1) == (t2, e2)
    LetTerm e1 t1 _ == LetTerm e2 t2 _  = (t1, e1) == (t2, e2)
    TermToken t1 == TermToken t2 = t1 == t2
    MixfixTerm l1 == MixfixTerm l2 = l1 == l2
    BracketTerm b1 l1 _ == BracketTerm b2 l2 _ = (b1, l1) == (b2, l2) 
    _ == _ = False

instance Eq Pattern where
    PatternVar l1 == PatternVar l2 = l1 == l2 
    PatternConstr i1 t1 l1 _ == PatternConstr i2 t2 l2 _ = 
	(i1, l1, t1) == (i2, l2, t2)
    PatternToken t1 == PatternToken t2 = t1 == t2
    BracketPattern b1 l1 _ == BracketPattern b2 l2 _ = (b1, l1) == (b2, l2) 
    TuplePattern l1 _ == TuplePattern l2 _ = l1 == l2
    MixfixPattern l1 == MixfixPattern l2 = l1 == l2
    TypedPattern p1 t1 _ == TypedPattern p2 t2 _ = (p1, t1) == (p2, t2) 
    AsPattern p1 q1 _ == AsPattern p2 q2 _ = (p1, q1) == (p2, q2) 
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

instance Eq Components where 
    Selector i1 p1 t1 _ _ == Selector i2 p2 t2 _ _ =
	(i1, t1, p1) == (i2, t2, p2)
    NoSelector t1 == NoSelector t2 = t1 == t2
    NestedComponents l1 _ == NestedComponents l2 _ = l1 == l2 
    _ == _ = False

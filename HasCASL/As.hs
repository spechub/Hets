
{- HetCATS/HasCASL/As.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   abstract syntax for HasCASL
   more liberal than HetCATS/HasCASL/Concrete-Syntax.txt
   annotations almost as in HetCATS/CASL/AS_Basic_CASL.hs v 1.8 
-}

module As where

import Id
import AS_Annotation 

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
               | AxiomItems [GenVarDecl] [Annoted Formula] [Pos]
               -- pos "forall" (if GenVarDecl not empty), dots 
                 deriving (Show, Eq)

data SigItems = TypeItems Instance [Annoted TypeItem] [Pos] -- including sort
              -- pos "type", ";"s
              | OpItems [Annoted OpItem] [Pos]
              -- pos "op", ";"s
              | PredItems [Annoted PredItem] [Pos]
              -- pos "pred", ";"s
                 deriving (Show, Eq)

-- "instance" indicator
data Instance = Instance | Plain deriving (Show, Eq)

data ClassItem = ClassItem ClassDecl [Annoted BasicItem] [Pos] 
                 -- pos "{", ";"s "}"
                 deriving (Show, Eq)

data ClassDecl = ClassDecl [ClassName] [Pos]
               -- pos ","s
               | SubclassDecl [ClassName] Class [Pos]
               -- pos ","s, "<"
               | ClassDefn ClassName Class [Pos]
               -- pos "="
               | DownsetDefn ClassName TypeVar Type [Pos] 
	       -- pos " =" "{", dot, "<", typeVar,  "}"
                 deriving (Show, Eq)
                          
data TypeItem  = TypeDecl [TypePattern] Kind [Pos]
               -- pos ","s
               | SubtypeDecl [TypePattern] Type [Pos]
               -- pos ","s, "<"
               | IsoDecl [TypePattern] [Pos]
               -- pos "="s
               | SubtypeDefn TypePattern Var Type (Annoted Formula) [Pos]
               -- pos "=", "{", ":", dot, "}"
               | AliasType TypePattern Kind PseudoType [Pos]
               -- pos ":="
	       | Datatype DatatypeDecl
                 deriving (Show, Eq)

data TypePattern = TypePattern TypeName [TypeArg] [Pos]
                 -- pos "("s, ")"s 
                 | TypePatternToken Token
                 | MixfixTypePattern [TypePattern]
                 | BracketTypePattern BracketKind [TypePattern] [Pos]
                 -- pos brackets 
                 | TypePatternArgs [TypeArg]
                   deriving (Show, Eq)

data PseudoType = SimplePseudoType Type 
                | PseudoType [TypeArgs] PseudoType [Pos]
                -- pos "\" "("s, ")"s, dot 
                  deriving (Show, Eq)

data Type = TypeConstrAppl TypeName Kind [Type] [Pos]  -- analysed
          | TypeVar TypeName Kind Int [Pos] -- analysed 
            -- Int > 0 means generalized
          | TypeToken Token
          | BracketType BracketKind [Type] [Pos]
          | KindedType Type Kind Pos
          -- pos ":"
          | MixfixType [Type] 
          | TupleType [Type] [Pos]
          -- pos "," (between type arguments)
	  | LazyType Type Pos
	  -- pos "?"
          | ProductType [Type] [Pos]
          -- pos crosses 
          | FunType Type Arrow Type [Pos]
          -- pos arrow
            deriving (Show, Eq)

data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Show, Eq)

data Pred = IsIn ClassName [Type]
              deriving (Show, Eq)

data Qual t = [Pred] :=> t
              deriving (Show, Eq)

-- no curried notation for bound variables 
data TypeScheme = SimpleTypeScheme Type
                | TypeScheme [TypeVarDecl] (Qual Type) [Pos]
                -- pos "forall", ";"s,  dot 
                  deriving (Show, Eq)

data Partiality = Partial | Total deriving (Show, Eq)

data OpItem = OpDecl [OpName] TypeScheme [OpAttr] [Pos]
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpName [Pattern] TypeScheme Partiality Term [Pos]
               -- pos "("s, ")"s, ":" or ":?", "="
              deriving (Show, Eq)

data PredItem = PredDecl [OpName] TypeScheme [Pos]
               -- pos ","s, ":", ","s
              | PredDefn OpName [Pattern] Formula [Pos]
               -- pos "("s, ")"s, "<=>"
              deriving (Show, Eq)

data BinOpAttr = Assoc | Comm | Idem deriving (Show, Eq)

data OpAttr = BinOpAttr BinOpAttr Pos | UnitOpAttr Term Pos deriving (Show, Eq)

data DatatypeDecl = DatatypeDecl 
                    TypePattern 
		    Kind
                    [Annoted Alternative] 
                    (Maybe Class) 
                    [Pos] 
		     -- pos "::=", "|"s, "deriving"
		     deriving (Show, Eq)

data Alternative = Constructor UninstOpName [Components] Partiality [Pos]
		   -- pos: "?"
		 | Subtype [Type] [Pos]
		   -- pos: "type", ","s
		   deriving (Show, Eq)

data Components = Selector UninstOpName Partiality Type SeparatorKind Pos 
		-- pos ",", ":" or ":?"
		| NoSelector Type
		| NestedComponents [Components] [Pos]
		  -- pos : "(", ";"s, ")"
		  deriving (Show, Eq)

data Quantifier = Universal | Existential | Unique
		  deriving (Show, Eq)

data TypeQual = OfType | AsType | InType deriving (Show, Eq)

data BracketKind = Parens | Squares | Braces deriving (Show, Eq)

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp deriving (Show, Eq)
data EqOp = EqualOp | ExEqualOp deriving (Show, Eq)

-- proper formulae only exist after static analysis
data Formula = TermFormula Term 	  
	     | ConnectFormula LogOp [Formula] [Pos]
	     -- pos not, "/\", "\/", impl, "<=>"
	     | EqFormula EqOp Term Term [Pos]
	     -- pos "=", "=e="
	     | DefFormula Term [Pos] 
	     -- pos "def"
	     | QuantifiedFormula Quantifier [VarDecl] Formula [Pos]
             -- pos quantifier, ";"s, dot
	     | PolyFormula [TypeVarDecl] Formula [Pos]
             -- pos "forall", ";"s, dot
	       deriving (Show, Eq)

-- parse quantified formulae as terms first
-- eases also parsing of formulae in parenthesis

data Term = CondTerm Term Formula Term [Pos]
	  -- pos "when", "else"
	  | QualVar Var Type [Pos]
	  -- pos "(", "var", ":", ")"
	  | QualOp InstOpName TypeScheme [Pos]
	  -- pos "(", "op", ":", ")" 
	  | ApplTerm Term Term [Pos]  -- analysed
	  -- pos?
	  | TupleTerm [Term] [Pos]
	  -- pos "(", ","s, ")"
	  | TypedTerm Term TypeQual Type Pos
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
	    deriving (Show, Eq)

data Pattern = PatternVars [VarDecl] [Pos]
             -- pos ";"s 
	     | PatternConstr InstOpName TypeScheme [Pattern] [Pos] 
	     -- constructor or toplevel operation applied to arguments
	     -- pos "("s, ")"s
             | PatternToken Token
	     | BracketPattern BracketKind [Pattern] [Pos]
	     -- pos brackets, ";"s, ","s
	     | TuplePattern [Pattern] [Pos]
	     -- pos ","s
	     | MixfixPattern [Pattern] -- or HO-Pattern
	     | TypedPattern Pattern Type [Pos]
	     -- pos ":"  
	     | AsPattern Pattern Pattern [Pos]
	     -- pos "@"
	       deriving (Show, Eq)

data ProgEq = ProgEq Pattern Term Pos deriving (Show, Eq)
	    -- pos "=" (or "->" following case-of)
-- ----------------------------------------------------------------------------
-- (type) var decls
-- ----------------------------------------------------------------------------

data SeparatorKind = Comma | Other deriving (Show, Eq)

data VarDecl = VarDecl Var Type SeparatorKind Pos deriving (Show, Eq)
	       -- pos "," or ":" 

-- currently TypeName is a simple Token and Kind is only a Class
data TypeVarDecl = TypeVarDecl TypeName Kind SeparatorKind Pos 
                   -- pos "," or ":" 
		   deriving (Show, Eq)

data TypeVarDecls = TypeVarDecls [TypeVarDecl] [Pos] deriving (Show, Eq)
		    -- pos "[", ";"s, "]"

data TypeArg = TypeArg TypeVar ExtClass SeparatorKind Pos
	       -- pos "," or ":" ("+" or "-" pos is moved to ExtClass)
	       deriving (Show, Eq)

data TypeArgs = TypeArgs [TypeArg] [Pos] deriving (Show, Eq)
	        -- pos ";"s

data GenVarDecl = GenVarDecl VarDecl
		| GenTypeVarDecl TypeVarDecl
		  deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- class
-- ----------------------------------------------------------------------------

data Variance = CoVar | ContraVar | InVar deriving (Show, Eq)

data ExtClass = ExtClass Class Variance Pos
                -- pos "+" or "-" (or nullPos)
	      | KindAppl Kind Kind  -- extension
		deriving (Show, Eq)

data ProdClass = ProdClass [ExtClass] [Pos] 
                 -- pos crosses 
		 deriving (Show, Eq)
                

data Kind = Kind [ProdClass] Class [Pos] 
	    -- pos "->"s (first order)
	    deriving (Show, Eq)

data Class = Downset Type   -- not parsed directly
	   | Intersection { iclass :: [ClassName], classPos :: [Pos] }  
	   -- pos "(", ","s, ")"
	     deriving (Show, Eq)

universe :: Class
universe = Intersection [] []

extUniverse :: ExtClass
extUniverse = ExtClass universe InVar nullPos
	       
nullKind :: Kind
nullKind = Kind [] universe []

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpName = OpName UninstOpName [TypeVarDecls] deriving (Show, Eq)

data Types = Types [Type] [Pos] deriving (Show, Eq) -- [TYPE, ..., TYPE]
data InstOpName = InstOpName UninstOpName [Types] deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeName = Id
type UninstOpName = Id

type Var = Id
type TypeVar = Token
type ClassName = Token


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
                  deriving (Show,Eq)

data BasicItem = SigItems SigItems
               | ProgItems [Annoted ProgEq] [Pos]
               -- pos "program", ";"s
               | ClassItems Instance [Annoted ClassItem] [Pos]
               -- pos "class", ";"s
               | GenVarItems [GenVarDecl] [Pos]
               -- pos "var", ";"s
               | FreeDatatype [Annoted DatatypeDecl] [Pos]
               -- pos "free", "type", ";"s
               | GenItems [Annoted BasicItem] [Pos] 
               -- pos "generated" "{", ";"s, "}"
               -- or "generated" "type" ";"s
               | LocalVarAxioms [GenVarDecl] [Annoted Term] [Pos]
               -- pos "forall" , dots 
               | AxiomItems [Annoted Term] [Pos]
               -- pos dots
                 deriving (Show,Eq)

data SigItems = TypeItems Instance [Annoted TypeItem] [Pos] -- including sort
              -- pos "type", ";"s
              | OpItems [Annoted OpItem] [Pos]              -- including pred
              -- pos "op"/"pred", ";"s
              | Datatype [Annoted DatatypeDecl] [Pos]
              -- pos "type", ";"s
                 deriving (Show,Eq)

-- "instance" indicator
data Instance = Instance | Plain deriving (Show,Eq)

data ClassItem = ClassItem ClassDecl [Annoted BasicItem] [Pos] 
                 -- pos "{", ";"s "}"
                 deriving (Show,Eq)

data ClassDecl = ClassDecl [ClassName] [Pos]
               -- pos ","s
               | SubclassDecl [ClassName] Class [Pos]
               -- pos ","s, "<"
               | ClassDefn ClassName Class [Pos]
               -- pos "="
                 deriving (Show,Eq)
                          
data TypeItem  = TypeDecl [TypePattern] Kind [Pos]
               -- pos ","s
               | SubtypeDecl [TypePattern] [Type] [Pos]
               -- pos ","s, "<"
               | IsoDecl [TypePattern] [Pos]
               -- pos "="s
               | SubtypeDefn TypePattern Var Type Term [Pos]
               -- pos "=", "{", ":", dot, "}"
               | AliasType TypePattern PseudoType [Pos]
               -- pos ":="
                 deriving (Show,Eq)

data TypePattern = TypePattern TypeName TypeArgs [Pos]
                 -- pos "("s, ")"s 
                 | TypePatternToken Token       
                 | BracketTypePattern BracketKind TypePattern [Pos]
                 -- pos brackets 
                 | TypePatternArgs TypeArgs
                   deriving (Show,Eq)

data PseudoType = SimplePseudoType Type 
                | PseudoType [TypeArgs] PseudoType [Pos]
                -- pos "\" "("s, ")"s, dot 
                  deriving (Show,Eq)

data Type = TypeConstrAppl TypeName Kind [Type] [Pos]  -- analysed
          | TypeToken Token
          | BracketType BracketKind Type [Pos]
          -- pos brackets 
          | KindedType Type Kind [Pos]
          -- pos ":"
          | MixfixType [Type] 
          | TupleType [Type] [Pos]
          -- pos "," (between type arguments)
          | ProductType [Type] [Pos]
          -- pos crosses or "(" and ")" (for the unit type)
          | FunType Type Arrow Type [Pos]
          -- pos arrow
            deriving (Show,Eq)

data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Show,Eq)

-- no curried notation for bound variables 
data TypeScheme = SimpleTypeScheme Type
                | TypeScheme TypeVarDecls TypeScheme [Pos]
                -- pos "forall", dot 
                  deriving (Show,Eq)

data PartialKind = Partial | Total deriving (Show,Eq)

data OpItem = OpDecl [OpName] TypeScheme [OpAttr] [Pos]
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpName [Pattern] TypeScheme Term [Pos]
               -- pos "("s, ")"s, ":" or ":?", "="
               -- or "(", ")", "<=>"
              deriving (Show,Eq)

data BinOpAttr = Assoc | Comm | Idem deriving (Show,Eq)

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term deriving (Show,Eq)

data DatatypeDecl = DatatypeDecl 
                    TypePattern 
                    [Annoted Alternative] 
                    (Maybe Class) 
                    [Pos] 
		     -- pos "::=", "|"s, "deriving"
		     deriving (Show,Eq)

data Alternative = Constructor UninstOpName [Components] PartialKind [Pos]
		   -- pos: "?"
		 | Subtype Type SeparatorKind [Pos]
		   -- pos: "type", "," or "|"
		   deriving (Show,Eq)

data Components = Selector UninstOpName PartialKind Type SeparatorKind [Pos] 
		-- pos ",", ":" or ":?"
		| NoSelector Type 
		| NestedComponents [Components]  [Pos]
		  -- pos : "(", ";"s, ")"
		  deriving (Show,Eq)

data Quantifier = Universal | Existential | Unique
		  deriving (Show,Eq)

data TypeQual = OfType | AsType | InType deriving (Show,Eq)

data BracketKind = Parens | Squares | Braces deriving (Show,Eq)

type Formula = Term

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp deriving (Show,Eq)
data EqOp = EqualOp | ExEqualOp deriving (Show,Eq)

data Term = CondTerm Term Formula Term [Pos]
	  -- pos "when", "else"
	  | ConnectFormula LogOp [Formula] [Pos]
	  -- pos not, "/\", "\/", impl, "<=>"
	  | EqFormula EqOp Term Term [Pos]
	  -- pos "=", "=e="
	  | DefFormula Term [Pos] 
	  -- pos "def"
	  | QualVar Var Type [Pos]
	  -- pos "(", "var", ":", ")"
	  | QualOp InstOpName TypeScheme [Pos]
	  -- pos "(", "op", ":", ")" 
	  | ApplTerm Term Term [Pos]  -- analysed
	  -- pos?
	  | TupleTerm [Term] [Pos]
	  -- pos "(", ","s, ")"
	  | TypedTerm Term TypeQual Type [Pos]
	  -- pos ":", "as" or "in"
	  | QuantifiedTerm Quantifier [VarDecl] Term [Pos]
          -- pos quantifier, ";"s, dot
	  | PolyTerm TypeVarDecls Term [Pos]
          -- pos "forall", dot
	  | LambdaTerm [Pattern] PartialKind Term [Pos]
          -- pos "\", dot (plus "!") 
	  | CaseTerm Term [ProgEq] [Pos]
	  -- pos "case", "of", "|"s 
	  | LetTerm [ProgEq] Term [Pos]
	  -- pos "let", ";"s, "in"
	  | TermToken Token
          | MixfixTerm [Term]
	  | TypeMixfixTerm TypeQual Type [Pos]
	  -- pos ":", "as" or "in"
	  | BracketTerm BracketKind [Term] [Pos]
	  -- pos brackets, ","s 
	    deriving (Show,Eq)

data Pattern = PatternVar Var Type SeparatorKind [Pos]
             -- pos "," or "colon" 
	     | PatternConstr InstOpName TypeScheme [Pattern] [Pos] 
	     -- constructor or toplevel operation applied to arguments
	     -- pos "("s, ")"s
             | PatternToken Token
	     | BracketPattern BracketKind Pattern [Pos]
	     -- pos brackets
	     | TuplePattern [Pattern] [Pos]
	     -- pos ";"s (or ","s)
	     | MixfixPattern [Pattern] 
	     | TypedPattern Pattern Type [Pos]     -- analysed
	     -- pos ":"  
	     | TypeMixfixPattern Type [Pos]
	     -- pos ":"  
	     | AsPattern Var Type Pattern [Pos]    -- analysed
	     -- pos ":", "@"
	     | AsMixfixPattern Pattern [Pos]
	     -- pos "@"
	       deriving (Show,Eq)

data ProgEq = ProgEq Pattern Term [Pos] deriving (Show,Eq)
	    -- pos "=" (or "->" following case-of)
-- ----------------------------------------------------------------------------
-- (type) var decls
-- ----------------------------------------------------------------------------

data SeparatorKind = Comma | Other deriving (Show,Eq)

data VarDecl = VarDecl Var Type SeparatorKind [Pos] deriving (Show,Eq)
	       -- pos "," or ":" 

data TypeVarDecl = TypeVarDecl TypeVar Class SeparatorKind [Pos] 
                   -- pos "," or ":" 
		   deriving (Show,Eq)

data TypeVarDecls = TypeVarDecls [TypeVarDecl] [Pos] deriving (Show,Eq)
		    -- pos ";"s

data TypeArg = TypeVars TypeVar ExtClass SeparatorKind [Pos]
	       -- pos "," or ":" plus "+" or "-" if given with TypeVar  
	       deriving (Show,Eq)

data TypeArgs = TypeArgs [TypeArg] [Pos] deriving (Show,Eq)
	      -- pos ";"s 

data GenVarDecl = GenVarDecl VarDecl
		| GenTypeVarDecl TypeVarDecl
		  deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- class
-- ----------------------------------------------------------------------------

data Variance = CoVar | ContraVar | InVar deriving (Show,Eq)

data ExtClass = ExtClass Class Variance [Pos] deriving (Show,Eq)
	        -- pos "+" or "-"

data ProdClass = ProdClass [ExtClass] [Pos] deriving (Show,Eq)
                 -- pos crosses 

data Kind = Kind [ProdClass] Class [Pos] deriving (Show,Eq)
	    -- pos "->"s (first order)
    
dummyTypeVar = Token "a" nullPos -- for Downset

data Class = Universe [Pos] -- pos "type" (or missing)
	   | ClassName ClassName
           | Downset TypeVar Type [Pos] 
	   -- pos "{", dot, "<", typeVar,  "}"
	   | Intersection [Class] [Pos]  
	   -- pos "(", ","s, ")"
	     deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpName = OpName UninstOpName [TypeVarDecls] [Pos] deriving (Show,Eq)

data Types = Types [Type] [Pos] deriving (Show,Eq) -- [TYPE, ..., TYPE]
data InstOpName = InstOpName UninstOpName [Types] Pos deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeName = Id
type UninstOpName = Id

type Var = Id
type TypeVar = Token
type ClassName = Token

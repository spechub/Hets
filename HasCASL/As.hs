
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

data BasicItem = TypeItem Instance [Annoted TypeItem] [Pos] -- including sort
	       | OpItem [Annoted OpItem] [Pos]              -- including pred
	       | ProgItem [Annoted ProgEq] [Pos]
	       | ClassItem Instance [Annoted ClassItem] [Pos]
	       -- pos: class, semi colons
	       | GenVarItems [GenVarDecl] [Pos]
	       -- pos: var, semi colons
	       | Datatype GenKind [Annoted DatatypeDecl] [Pos]
	       -- pos: free, type, semi colons
	       | GenItems [Annoted BasicItem] [Pos] 
		   -- pos: generated, opt. braces (type in Datatype_items)
	       | LocalVarAxioms [GenVarDecl] [Annoted Term] [Pos]
		   -- pos: forall, dots
	       | AxiomItem [Annoted Term] [Pos]
	       -- pos: dots
		 deriving (Show,Eq)

data Instance = Instance | Plain deriving (Show,Eq)

-- looseness of a datatype
data GenKind = Free | Generated | Loose deriving (Show,Eq)      
			    
data ClassItem = ClassGroup ClassDecl [Annoted BasicItem] [Pos] 
		 deriving (Show,Eq)

data ClassDecl = ClassDecl [ClassName] [Pos]
	         -- pos: commas
	       | SubclassDecl [ClassName] Class [Pos]
	       | IsoClassDecl [ClassName] [Pos]
		-- pos: commas, <
               | ClassDefn ClassName Class [Pos]
		 deriving (Show,Eq)

			  
data TypeItem  = TypeDecl [TypePattern] Kind [Pos]
	       | SubtypeDecl [TypePattern] [Type] [Pos]
	       | IsoDecl [TypePattern] [Pos]
	       | SubtypeDefn TypePattern Var Type Term [Pos]
               | AliasType TypePattern PseudoType [Pos]
	         -- pos: commas
		 deriving (Show,Eq)


data TypeArg = TypeVars [TypeVar] ExtClass [Pos]
	     | TypeExtVars [TypeExtVar] Class [Pos] 
	       deriving (Show,Eq)

data TypeExtVar = TypeExtVar TypeVar Variance Pos deriving (Show,Eq)

data TypePattern = TypeDeclPattern TypeName TypeArgs [Pos]
		 | TypePattern [PrimTypePattern]
		   deriving (Show,Eq)

data PrimTypePattern = TypePatternToken Token
		     | BracketTypePattern BracketKind [PrimTypePattern] [Pos]
		     | TypePatternArg TypeVar ExtClass [Pos]
		     | TypePatternArgs TypeArgs [Pos]
		       deriving (Show,Eq)

data TypeArgs = TypeArgs [TypeArg] [Pos] deriving (Show,Eq)

data PseudoType = PseudoType [TypeArgs] Type [Pos] 
		| NestedPseudoType [TypeArgs] PseudoType [Pos] 
		  deriving (Show,Eq)

data Type = TypeToken Token
	  | BracketType BracketKind [Type] [Pos]
          | ClassifiedType Type Class [Pos]
	  | MixfixType [Type] 
	  | ProductType [Type] [Pos]
	  | FunType [Type] [Arrow] [Pos]
	    deriving (Show,Eq)

data Arrow = FunArr| PFunArr | ContFun | PContFun deriving (Show,Eq)

data TypeScheme = TypeScheme [TypeVarDecl] Type [Pos]
		| NestedTypeScheme [TypeVarDecl] TypeScheme [Pos]
		  deriving (Show,Eq)

data PartialKind = Partial | Total deriving (Show,Eq)

data OpItem = OpDecl [OpName] TypeScheme [OpAttr] [Pos]
	       -- pos: commas, colon,
	    | OpDefn OpName [ArgDecls] PartialKind TypeScheme Term [Pos]
	       -- pos: "="
	      deriving (Show,Eq)

data ArgDecls = ArgsDecls [VarDecl] [Pos] deriving (Show,Eq)

data BinOpAttr = Assoc | Comm | Idem deriving (Show,Eq)

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term deriving (Show,Eq)

data DatatypeDecl = DatatypeDecl TypePattern [Annoted Alternative] [Pos] 
		     -- pos: "::=", "|"s
		     deriving (Show,Eq)

data Alternative = Constructor UninstOpName [Components] PartialKind [Pos]
		   -- pos: "(" ... ")" ... "(" ... ")" , "?"
		 | Subtypes [Type] [Pos]
		   -- pos: sort/type, commas
		   deriving (Show,Eq)

data Components = Selector [UninstOpName] PartialKind Type [Pos] 
		| NestedComponents [Components] [Pos]
		  -- pos : "(" ; ... ;  ")"
		  deriving (Show,Eq)

data Quantifier = Universal | Existential | Unique
		  deriving (Show,Eq)

data TypeQual = OfType | AsType | InType deriving (Show,Eq)

data BracketKind = Parens | Squares | Braces deriving (Show,Eq)

data Term = MixfixToken Token
	  | QualVar Var Type [Pos]
	  | QualOp InstOpName Type [Pos]
	  | TypedTerm Term TypeQual Type [Pos]
          | MixfixTerm [Term]
	  | BracketTerm BracketKind [Term] [Pos]
	  | QuantifiedTerm Quantifier [GenVarDecl] Term [Pos]
	  | LambdaTerm [Pattern] PartialKind Term [Pos]
	  | CaseTerm Term [ProgEq] [Pos]
	  | LetTerm [ProgEq] Term [Pos]
	    deriving (Show,Eq)

data ProgEq = ProgEq Pattern Term [Pos] deriving (Show,Eq)

data SeparatorKind = Comma | Semicolon deriving (Show,Eq)

data Pattern = PatternToken Token
	     | BracketPattern BracketKind Pattern [Pos]
	     | TuplePattern SeparatorKind [Pattern] [Pos]
	     | MixfixPattern [Pattern] 
	     | TypedPattern Pattern Type [Pos]
	     | AsPattern Pattern Pattern [Pos]
	       deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- type var decls
-- ----------------------------------------------------------------------------

data VarDecl = VarDecl [Var] Type [Pos] deriving (Show,Eq)

data TypeVarDecl = TypeVarDecl [TypeVar] Class [Pos] deriving (Show,Eq)

data GenVarDecl = GenVarDecl [Var] Type [Pos]
		| SureTypeVarDecl [TypeVar] Class [Pos]
		  deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- class
-- ----------------------------------------------------------------------------

data Variance = CoVar | ContraVar | InVar deriving (Show,Eq)

data ExtClass = ExtClass Class Variance Pos deriving (Show,Eq)

data ProdClass = ProdClass [ExtClass] [Pos] deriving (Show,Eq)

data Kind = Kind [ProdClass] Class [Pos] deriving (Show,Eq)

data Dir = Up | Down deriving (Show,Eq)  -- < oder > 

dummyTypeVar = Token "a" nullPos -- for TypeVarDecl

data Class = Universe [Pos] -- "type" or missing
	   | ClassName ClassName
           | TypeSet Dir TypeVar Type [Pos] -- { a . a < TYPE }  
	   | InterSection [Class] [Pos]  -- ( CLASS, ..., CLASS )
	     deriving (Show,Eq)

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpName = OpName [TypeVarDecl] [Pos] deriving (Show,Eq)

data Types = Types [Type] [Pos] deriving (Show,Eq) -- [TYPE, ..., TYPE]
data InstOpName = InstOpName [Types] Pos deriving (Show,Eq) -- curried

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeName = Id
type UninstOpName = Id

type Var = Id
type TypeVar = Token
type ClassName = Token

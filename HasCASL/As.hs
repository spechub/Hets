
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

data ClassDecl = ClassDecl [ClassId] [Pos]
               -- pos ","s
               | SubclassDecl [ClassId] Class [Pos]
               -- pos ","s, "<"
               | ClassDefn ClassId Class [Pos]
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
               | SubtypeDefn TypePattern Var Type (Annoted Formula) [Pos]
               -- pos "=", "{", ":", dot, "}"
               | AliasType TypePattern Kind PseudoType [Pos]
               -- pos ":="
	       | Datatype DatatypeDecl
                 deriving (Show, Eq)

data TypePattern = TypePattern TypeId [TypeArg] [Pos]
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

data Type = TypeName TypeId Int  -- analysed
            -- Int > 0 means generalized
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
            deriving (Show, Eq)

data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr 
             deriving (Show, Eq)

data Pred = IsIn ClassId [Type]
              deriving (Show, Eq)

data Qual t = [Pred] :=> t
              deriving (Show, Eq)

-- no curried notation for bound variables 
data TypeScheme = SimpleTypeScheme Type
                | TypeScheme [TypeArg] (Qual Type) [Pos]
                -- pos "forall", ";"s,  dot 
                  deriving (Show, Eq)

data Partiality = Partial | Total deriving (Show, Eq)

data OpItem = OpDecl [OpId] TypeScheme [OpAttr] [Pos]
               -- pos ","s, ":", ","s, "assoc", "comm", "idem", "unit"
            | OpDefn OpId [Pattern] TypeScheme Partiality Term [Pos]
               -- pos "("s, ")"s, ":" or ":?", "="
              deriving (Show, Eq)

data PredItem = PredDecl [OpId] TypeScheme [Pos]
               -- pos ","s, ":", ","s
              | PredDefn OpId [Pattern] Formula [Pos]
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

data Alternative = Constructor UninstOpId [Components] Partiality [Pos]
		   -- pos: "?"
		 | Subtype [Type] [Pos]
		   -- pos: "type", ","s
		   deriving (Show, Eq)

data Components = Selector UninstOpId Partiality Type SeparatorKind Pos 
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
	     | PolyFormula [TypeArg] Formula [Pos]
             -- pos "forall", ";"s, dot
	       deriving (Show, Eq)

-- parse quantified formulae as terms first
-- eases also parsing of formulae in parenthesis

data Term = CondTerm Term Formula Term [Pos]
	  -- pos "when", "else" (or if-then-else)
	  | QualVar Var Type [Pos]
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
	    deriving (Show, Eq)

data Pattern = PatternVars [VarDecl] [Pos]
             -- pos ";"s 
	     | PatternConstr InstOpId TypeScheme [Pattern] [Pos] 
	     -- constructor or toplevel operation applied to arguments
	     -- pos "("s, ")"s
             | PatternToken Token
	     | BracketPattern BracketKind [Pattern] [Pos]
	     -- pos brackets, ";"s, ","s
	     | TuplePattern [Pattern] [Pos]
	     -- pos ","s
	     | MixfixPattern [Pattern] -- or HO-Pattern
	     | TypedPattern Pattern Type [Pos]	     -- pos ":"  
	     | AsPattern Pattern Pattern [Pos]
	     -- pos "@"
	       deriving (Show, Eq)

data ProgEq = ProgEq Pattern Term Pos deriving (Show, Eq)
	    -- pos "=" (or "->" following case-of)
-- ----------------------------------------------------------------------------
-- (type) var decls
-- ----------------------------------------------------------------------------

data SeparatorKind = Comma | Other deriving (Show, Eq)

data VarDecl = VarDecl Var Type SeparatorKind [Pos] deriving (Show, Eq)
	       -- pos "," or ":" 

data TypeVarDecls = TypeVarDecls [TypeArg] [Pos] deriving (Show, Eq)
		    -- pos "[", ";"s, "]"

data TypeArg = TypeArg TypeId Kind SeparatorKind [Pos]
	       -- pos "," or ":" ("+" or "-" pos is moved to ExtClass)
	       deriving (Show, Eq)

data TypeArgs = TypeArgs [TypeArg] [Pos] deriving (Show, Eq)
	        -- pos ";"s

data GenVarDecl = GenVarDecl VarDecl
		| GenTypeVarDecl TypeArg
		  deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- class
-- ----------------------------------------------------------------------------

data Variance = CoVar | ContraVar | InVar deriving (Show, Eq)

data Kind = PlainClass Class
            | ExtClass Kind Variance [Pos]
	     -- pos "+" or "-" 
	    | ProdClass [Kind] [Pos] 
	    -- pos crosses
	    | KindAppl Kind Kind [Pos]
	    -- pos "->" 
	    deriving (Show, Eq)

data Class = Downset Type   -- not parsed directly
	   | Intersection { iclass :: [ClassId], classPos :: [Pos] }  
	   -- pos "(", ","s, ")"
	     deriving (Show, Eq)

universe :: Class
universe = Intersection [] []

nullKind :: Kind
nullKind = PlainClass universe

-- ----------------------------------------------------------------------------
-- op names
-- ----------------------------------------------------------------------------

data OpId = OpId UninstOpId [TypeVarDecls] deriving (Show, Eq)

data Types = Types [Type] [Pos] deriving (Show, Eq) -- [TYPE, ..., TYPE]
data InstOpId = InstOpId UninstOpId [Types] deriving (Show, Eq)

-- ----------------------------------------------------------------------------
-- ids
-- ----------------------------------------------------------------------------

type TypeId = Id
type UninstOpId = Id

type Var = Id
type ClassId = Id -- TOKEN-ID (one token with compound list, like CASL sorts)

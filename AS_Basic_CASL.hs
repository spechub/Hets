module AS_Basic where

data BASIC_SPEC = Basic_spec [BASIC_ITEMS]
		  deriving (Show,Eq)

data BASIC_ITEMS = Sig_items SIG_ITEMS
		 | Free_datatype [DATATYPE_DECL]
		 | Sort_gen [SIG_ITEMS]
		 | Var_items [VAR_DECL]
		 | Local_var_axioms([VAR_DECL],[TERM])
		 | Axiom_items [TERM]
		   deriving (Show,Eq)

data SIG_ITEMS = Sort_items [SORT_ITEM] 
	       | Op_items [OP_ITEM]
	       | Pred_items [OP_ITEM]
	       | Datatype_items [DATATYPE_DECL]
		 deriving (Show,Eq)

data SORT_ITEM = Sort_decl [TYPE]
	       | Sub_sort_decl([TYPE],TYPE)
	       | Iso_decl [TYPE]
	       | Subsort_defn(TYPE,VAR,TYPE,TERM)
		 deriving (Show,Eq)

data OP_ITEM = Op_decl([OP_NAME],TYPE,[OP_ATTR])
	     | Op_defn(OP_NAME,TYPE,TERM)
	       deriving (Show,Eq)

data TYPE = Type(TYPE_NAME,[TYPE])
	    deriving (Show,Eq)

data OP_ATTR = Assoc_op_attr | Common_op_attr | Idem_op_attr
	     | Unit_op_attr TERM
	       deriving (Show,Eq)
{- Aufgegangen in OP_ITEM
data PRED_ITEM = Pred_decl([PRED_NAME],PRED_TYPE)
	       | Pred_defn(PRED_NAME,PRED_HEAD,FORMULA)
		 deriving (Show,Eq)

data PRED_TYPE = Pred_type [SORT]
		 deriving (Show,Eq)

data PRED_HEAD = Pred_head [ARG_DECL]
		 deriving (Show,Eq)
-}
data DATATYPE_DECL = Datatype_decl(TYPE,[ALTERNATIVE])
		     deriving (Show,Eq)

data ALTERNATIVE = Construct(TOTALITY,OP_NAME,[COMPONENTS])
		 | Subsorts [TYPE]
		   deriving (Show,Eq)

data COMPONENTS = Select(TOTALITY,[OP_NAME],TYPE)
		| No_select TYPE
		  deriving (Show,Eq)

data VAR_DECL = Var_decl([VAR],TYPE)
		deriving (Show,Eq)

-- The Mixfix-constructor also contains 

data TERM = Mixfix(BRACKET_KIND,[TERM])
	  | Qual_name(QUAL_KIND,ID,TYPE)
	  | Typed_term(CAST_KIND,TERM,TYPE)
	  | Token_or_place TOKEN_OR_PLACE
	  | Literal(LITERAL_KIND,String)
	  | Binding(BINDER,[VAR_DECL],TERM)
	    deriving (Show,Eq)

data CAST_KIND = Sorted_term | Membership | Cast
		 deriving (Show,Eq)

data BRACKET_KIND = Brack | Paren | Brace
		    deriving (Show,Eq)

data QUAL_KIND = Var | Pred | Op
		 deriving (Show,Eq)

data BINDER = Lambda(NOTATION,TOTALITY)
	    | Forall | Exists | Exists_uniq
	      deriving (Show,Eq)

data NOTATION = Arg_decl | Explicit_lambda
		deriving (Show,Eq)

data TOTALITY = Partial | Total
		deriving (Show,Eq)

data USER = User | System
	    deriving (Show,Eq)

data LITERAL_KIND = String | Fraction | Floating | Digits
		    deriving (Show,Eq)

type TYPE_NAME = String

type OP_NAME = ID

type VAR = SIMPLE_ID

type SIMPLE_ID = String
    
data ID = Token_id TOKEN -- extra constructor
	| Token_places [TOKEN_OR_PLACE]
--	| Comp_token_id(TOKEN,[ID])
	| Comp_id([TOKEN_OR_PLACE],[ID])
	  deriving (Show,Eq)

type TOKEN = String

data TOKEN_OR_PLACE = Place
		    | Token TOKEN
		      deriving (Show,Eq)

----- 
data SYMB_ITEMS = Symb_items(SYMB_KIND,[SYMB])
		  deriving (Show,Eq)

data SYMB_MAP_ITEMS = Symb_map_items(SYMB_KIND,[SYMB_OR_MAP])
		      deriving (Show,Eq)

data SYMB_OR_MAP = Symb SYMB
		 | Symb_map(SYMB,SYMB) 
		   deriving (Show,Eq)

data SYMB_KIND = Implicit | Sorts_kind 
	       | Ops_kind | Preds_kind
		 deriving (Show,Eq)

data SYMB = Symb_id ID
	  | Qual_id(ID,TYPE)
	    deriving (Show,Eq)


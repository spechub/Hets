module AS_Architecture where
import AS_Basic
import AS_Structured

data ARCH_SPEC_DEFN = Arch_spec_defn(ARCH_SPEC_NAME,ARCH_SPEC)
		      deriving (Show,Eq)

data ARCH_SPEC = Basic_arch_spec([UNIT_DECL_DEFN],RESULT_UNIT)
	       | Arch_spec_name ARCH_SPEC_NAME
		 deriving (Show,Eq)

data UNIT_DECL_DEFN = Unit_decl(UNIT_NAME,UNIT_SPEC,UNIT_IMPORTED)
		    | UNIT_DEFN UNIT_DEFN
		      deriving (Show,Eq)

data UNIT_DEFN = Unit_defn(UNIT_NAME,UNIT_EXPRESSION)
		 deriving (Show,Eq)
data UNIT_IMPORTED = Unit_imported [UNIT_TERM]
		     deriving (Show,Eq)

data UNIT_SPEC_DEFN = Unit_spec_defn(SPEC_NAME,UNIT_SPEC)
		      deriving (Show,Eq)

data UNIT_SPEC = Unit_type([SPEC],SPEC)
	       | Spec_name SPEC_NAME
	       | Arch_unit_spec ARCH_SPEC
	       | Closed_unit_spec UNIT_SPEC 
		 deriving (Show,Eq)

data RESULT_UNIT = Result_unit UNIT_EXPRESSION
		   deriving (Show,Eq)

data UNIT_EXPRESSION = Unit_expression([UNIT_BINDING],UNIT_TERM)
		       deriving (Show,Eq)

data UNIT_BINDING = Unit_binding(UNIT_NAME,UNIT_SPEC)
		    deriving (Show,Eq) 

data UNIT_TERM = Unit_reduction(UNIT_TERM,RESTRICTION)
	       | Unit_translation(UNIT_TERM,RENAMING)
	       | Amalgamation [UNIT_TERM]
	       | Local_unit([UNIT_DEFN],UNIT_TERM)
	       | Unit_appl(UNIT_NAME,[FIT_ARG_UNIT])
		 deriving (Show,Eq)

data FIT_ARG_UNIT = Fit_arg_unit(UNIT_TERM,[SYMB_MAP_ITEMS])
		    deriving (Show,Eq)

type ARCH_SPEC_NAME = SIMPLE_ID
type UNIT_NAME = SIMPLE_ID
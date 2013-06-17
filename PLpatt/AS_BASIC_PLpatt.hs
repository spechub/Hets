module PLpatt.AS_BASIC_PLpatt where

type Id = String
type Var = Int
data Bool' = Or Bool' Bool' | And Bool' Bool' | Not Bool' | True'  | False'  | Prop_bool Id deriving Show
data Prop = Prop Id deriving Show
data Axiom = Axiom Id Bool' deriving Show
data Decl = Prop_decl Prop | Axiom_decl Axiom deriving Show
data Symb = Symb{sname :: Id}

newtype Basic_spec = Basic_spec [String] deriving Show
--newtype Basic_spec = Basic_spec [Decl] deriving Show

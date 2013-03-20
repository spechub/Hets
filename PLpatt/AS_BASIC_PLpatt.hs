module PLpatt.AS_BASIC_PLpatt where

--import Common.Id as Id


type Id = String
type Var = Int
data Bool' = Or Bool' Bool' | And Bool' Bool' | Not Bool' | True'  | False'  | Prop_bool Id
data Prop = Prop Id
data Axiom = Axiom Id Bool'
data Decl = Prop_decl Prop | Axiom_decl Axiom
type Basic_spec = [Decl]
data Symb = Symb{sname :: Id}


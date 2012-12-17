module PLpatt.AS_BASIC_PLpatt where

--import Common.Id as Id


type Id = String
type Var = Int
data Form = Or Form Form | And Form Form | Not Form | Prop_bool Id
data Prop = Prop Id
data Axiom = Axiom Id Form
data Decl = Prop_decl Prop | Axiom_decl Axiom
type Basic_spec = [Decl]
data Symbol = Symb{sname :: Id}


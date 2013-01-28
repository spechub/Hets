module PLpatt.AS_BASIC_PLpatt where

type Id = String
type Var = Int
data Form = Prop_bool Id
data Prop = Prop Id
data Axiom = Axiom Id Form
data Decl = Prop_decl Prop | Axiom_decl Axiom
type Basic_spec = [Decl]
data Symbol = Symbol{ sname :: Id}

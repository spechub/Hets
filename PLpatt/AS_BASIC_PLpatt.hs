module PLpatt.AS_BASIC_PLpatt 
        ( Basic_spec (..)
        , Form (..)
        , Decl (..)
        , Symb (..)
        ) where

--import Common.Id as Id


type Id = String
type Var = Int
data Form = Or Form Form | And Form Form | Not Form | True  | False  | Prop_bool Id
data Prop = Prop Id
data Axiom = Axiom Id Form
data Decl = Prop_decl Prop | Axiom_decl Axiom
newtype Basic_spec = Basic_spec [Decl]
data Symb = Symb{sname :: Id}


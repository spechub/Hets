{-# LANGUAGE DeriveDataTypeable #-}
module PLpatt.AS_BASIC_PLpatt where

import Data.Typeable

type Id = String
type Var = Int
data Bool' = True'  | False'  | And Bool' Bool' | Or Bool' Bool' | Not Bool' | Impl Bool' Bool' | Equiv Bool' Bool'
 deriving ( Show, Typeable, Eq, Ord)
data Dot = Dot Id Bool'
 deriving ( Show, Typeable, Eq)
data Prop = Prop Id
 deriving ( Show, Typeable, Eq)
data Decl = Dot_decl Dot | Prop_decl Prop
 deriving ( Show, Typeable, Eq)
data Symb = Symb{sname :: Id} deriving ( Show, Typeable, Eq, Ord)


newtype Basic_spec = Basic_spec [String] deriving (Show, Typeable)

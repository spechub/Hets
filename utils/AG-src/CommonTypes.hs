{- UU_AG
 - Copyright:  S. Doaitse Swierstra, Arthur I. Baars and Andres Loeh
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb,andres}@cs.uu.nl -}
module CommonTypes where

import UU_Pretty
import UU_Maps


type Attributes  = Map Name String
type AttrNames   = [(Name,String,(String,String))]
type TypeSyns    = [(Nonterminal,String)]
type UseMap      = Map Nonterminal (Map Name (String,String))
type Fields      = [(Name,String)]

type Name        = String
type Nonterminal = String
type Constructor = String

type AttrEnv = ( [Name]
               , [(Name,Name)]
               )

_LHS = "lhs"
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder  and Uni Bremen 2002-2003

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing Haskell's ModuleInfo

-}

module Haskell.PrintModuleInfo where

import Common.PrettyPrint
import Common.Lib.Pretty

import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.PPrint
import Haskell.Hatchet.AHsPretty as AP

instance PrettyPrint ModuleInfo where
  printText0 _ga _modInfo = text "module Dummy where"
             $$ text "import Prelude (undefined, Show, Eq, Ord, Bool)"
             $$ text "import MyLogic"

instance PrettyPrint AHsDecl where
    printText0 _ = text . AP.render . ppAHsDecl
instance PrettyPrint AHsName where
    printText0 _ = pprint

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
import Common.PPUtils
import Common.Lib.Pretty

import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.Env
import Haskell.Hatchet.PPrint
import Haskell.Hatchet.AHsPretty as AP

instance PrettyPrint ModuleInfo where
  printText0 ga modInfo = text "module" 
                                <+> pprint (moduleName modInfo)
                                <+> text "where" 
                          $$ pprintEnv (varAssumps modInfo)

instance PrettyPrint AHsDecl where
    printText0 _ = text . AP.render . ppAHsDecl
instance PrettyPrint AHsName where
    printText0 _ = pprint

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
import Common.Lib.Pretty as Pretty

import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.AnnotatedHsSyn

instance PrettyPrint ModuleInfo where
  printText0 _ modInfo = text "Module name" 
                                <+> text (show (moduleName modInfo)) 
                                <> comma
                          $+$ text "Variable Assumptions" 
                                <+> text (show (varAssumps modInfo))
                                <> comma
                          $+$ text "Data Constructor Assumptions" 
                                <+> text (show (dconsAssumps modInfo))
                                <> comma
                          $+$ text "Class Hierarchy" 
                                <+> text (show (classHierarchy modInfo))
                                <> comma
                          $+$ text "Kinds" 
                                <+> text (show (kinds modInfo))
                                <> comma
                          $+$ text "Synonyms" 
                                <+> text (show (synonyms modInfo))
                                <> comma
                          $+$ text "Infix Declarations" 
                                <+> text (show (infixDecls modInfo))
                                <> comma
                          $+$ text "Type Constructor Members" 
                                <+> text (show (tyconsMembers modInfo))
                                <> comma

instance PrettyPrint AHsDecl where
    printText0 _ = ptext . show

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
import Common.Lib.Pretty as Pretty

import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.Env
import Haskell.Hatchet.PPrint

instance PrettyPrint ModuleInfo where
  printText0 ga modInfo = text "module" 
                                <+> pprint (moduleName modInfo)
                                <+> text "where" 
                          $$ text "-- Functions" 
                          $$ pprintEnv (varAssumps modInfo)
                          $$ text "-- Constructors" 
			  $$ pprintEnv (dconsAssumps modInfo)
                          $$ text "-- Class Hierarchy" 
 			  $$ pprintEnv (classHierarchy modInfo)
                          $$ text "-- Kinds" 
                          $$ pprintEnv (kinds modInfo)
                          $$ text "-- Synonyms" 
                          $$ vcat (map (printText0 ga) $ synonyms modInfo)
                          $$ text "-- Infix Declarations" 
                          $$ vcat (map (printText0 ga) $ infixDecls modInfo)
                          $$ text "-- Type Constructor Members" 
                          $$ vcat (map ( \ (t, cs) -> 
				printText0 ga t 
				<+> char '='
				<+> listSep_text (space<>char '|') ga cs)
				   $ tyconsMembers modInfo)

instance PrettyPrint AHsDecl where
    printText0 _ = ptext . show
instance PrettyPrint AHsName where
    printText0 _ = pprint

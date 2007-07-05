{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

the TIModule analysis without timings and dumps

-}

module Haskell.Hatchet.TIHetsModule (tiModule) where

import Haskell.Hatchet.AnnotatedHsSyn
                                (AHsDecl,
                                 AHsModule)
import Haskell.Hatchet.TIMain   (TypeEnv,
                                 makeProgram)
import Haskell.Hatchet.KindInference
                                (KindEnv)
import Haskell.Hatchet.TidyModule (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)
import Haskell.Hatchet.TypeSigs (listSigsToSigEnv)
import Haskell.Hatchet.Class    (ClassHierarchy)
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.TIPhase

-- | type check a single module 

tiModule :: AHsModule                   -- syntax of module after parsing
         -> ModuleInfo                  -- info about imported entities
         -> (TypeEnv,          -- output variable assumptions 
                               -- (may be local, and pattern variables) 
             TypeEnv,          -- output data cons assumptions 
             ClassHierarchy,      -- output class Hierarchy 
             KindEnv,             -- output kinds 
             AHsModule,           -- renamed module 
             [AHsDecl])           -- synonyms defined in this module

tiModule modSyntax imports =
    let (renMod, _) = renameTM imports $ desugarTM imports $ 
                           tidyModule modSyntax
        kindInfo = getKindInfo renMod imports
        classHier = getClassHierarchy renMod imports kindInfo
        sigEnv = listSigsToSigEnv kindInfo $ getAllTypeSigs renMod
        localDConsEnv = getLocalDConsEnv renMod kindInfo
        globalDConsEnv = getGlobalDConsEnv localDConsEnv imports 
        prog = makeProgram sigEnv $ getProgramBgs renMod
        localVars = getLocalVarEnv renMod imports sigEnv kindInfo classHier 
                     globalDConsEnv prog
     in (localVars, 
         localDConsEnv,
         classHier,
         kindInfo, 
         tidyModuleToAHsModule renMod,
         tidyTyDecls renMod) 


{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

the TIModule analysis without timings and dumps

-}

module Haskell.Hatchet.TIHetsModule (tiModule) where

import Haskell.Hatchet.AnnotatedHsSyn
                                (ASrcLoc (..),
                                 bogusASrcLoc,
                                 AHsDecl,
                                 AHsName (..),
                                 AModule (..),
                                 AHsModule)


import qualified Haskell.Hatchet.PPrint as PPrint         (render)

import Haskell.Hatchet.Desugar  (desugarTidyModule)

import Haskell.Hatchet.TIMain   (getFunDeclsBg, TypeEnv,
                                 makeProgram,
                                 tiProgram)

import Haskell.Hatchet.Rename   (renameTidyModule,
                                 IdentTable,
                                 printIdentTable)

import Haskell.Hatchet.KindInference
                                (KindEnv,
                                 kiModule)

import Haskell.Hatchet.Representation
                                (Kind,
                                 Scheme,
                                 Assump (..))


import Haskell.Hatchet.DataConsAssump    (dataConsEnv)

import Haskell.Hatchet.Utils    (maybeGetDeclName,
                                 rJustify,
                                 lJustify,
                                 Binding (..),
                                 getAModuleName,
                                 getDeclName,
                                 fromAHsName,
                                 doDump)

import Haskell.Hatchet.FiniteMaps (toListFM,
                                 zeroFM,
                                 addToFM)

import Haskell.Hatchet.TidyModule (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)


import Haskell.Hatchet.TypeSigs (collectSigs,
                                 listSigsToSigEnv)


import Haskell.Hatchet.Class    ( --addInstancesToHierarchy,
                                 printClassHierarchy,
                                 -- instanceToTopDecls,
                                 addClassToHierarchy,
                                 ClassHierarchy,
                                 classMethodAssumps)

import Maybe    (mapMaybe)

import Haskell.Hatchet.Env      (listToEnv,
                                 getNamesFromEnv,
                                 Env,
                                 envToList,
                                 pprintEnv,
                                 joinEnv,
                                 showEnv)

import Haskell.Hatchet.Type     (assumpId)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.DependAnalysis (getBindGroups)

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


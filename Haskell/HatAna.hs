{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Here is the place where the class Logic is instantiated for Haskell.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Haskell.HatAna where

import Common.AS_Annotation 

import Haskell.HaskellUtils              (extractSentences)
import Haskell.ExtHaskellCvrt            

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
                                          joinModuleInfo,
                                          getTyconsMembers,
                                          getInfixDecls)
import Haskell.Hatchet.TIHetsModule      (tiModule)
import Haskell.Hatchet.AnnotatedHsSyn    
import Haskell.Hatchet.Env               (listToEnv,
                                          emptyEnv)
import Haskell.Hatchet.HaskellPrelude    (preludeDefs,
                                          tyconsMembersHaskellPrelude,
                                          preludeDataCons,
                                          preludeClasses,
                                          preludeTyconAndClassKinds,
                                          preludeInfixDecls,
                                          preludeSynonyms)
import Haskell.Hatchet.SynConvert        
import Haskell.Hatchet.HsParsePostProcess
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)
import Haskell.Hatchet.HsSyn             (HsDecl)
import Haskell.Hatchet.Type              (assumpToPair)

emptySign :: ModuleInfo
emptySign = ModuleInfo { varAssumps = emptyEnv,
                      moduleName = AModule "Empty",
		                -- error "Unspecified module name",
                      dconsAssumps = emptyEnv,
                      classHierarchy = emptyEnv,
                      tyconsMembers = [], 
                      kinds = emptyEnv,
                      infixDecls = [],
                      synonyms = [] }

hatAna :: [HsDecl] -> ModuleInfo -> (ModuleInfo, [Named AHsDecl])
hatAna hs sig = 
    let ahs = map toAHsDecl $ fixFunBinds $ cvrtHsDeclList hs
        aMod = AHsModule (moduleName sig) Nothing [] ahs
        (moduleEnv,
   	 dataConEnv,
   	 newClassHierarchy,
   	 newKindInfoTable,
   	 moduleRenamed,
   	 moduleSynonyms) = tiModule aMod sig
  	modInfo = sig {     varAssumps = moduleEnv, 
    			    dconsAssumps = dataConEnv, 
    			    classHierarchy = newClassHierarchy,
    			    kinds = newKindInfoTable,
    			    tyconsMembers = getTyconsMembers moduleRenamed,
    			    infixDecls = getInfixDecls moduleRenamed,
    			    synonyms = moduleSynonyms }
	in (modInfo, extractSentences moduleRenamed)


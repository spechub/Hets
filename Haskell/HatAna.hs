{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   todo:
     - write difference function for ModuleInfos
     - include Prelude (or undefined) during type inference

-}

module Haskell.HatAna where

import Common.AS_Annotation 

import Haskell.HaskellUtils              (extractSentences)
import Haskell.ExtHaskellCvrt            

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
					  emptyModuleInfo,
                                          getTyconsMembers,
                                          getInfixDecls)
import Haskell.Hatchet.TIHetsModule      (tiModule)
import Haskell.Hatchet.AnnotatedHsSyn    
import Haskell.Hatchet.Env               (emptyEnv)
import Haskell.Hatchet.SynConvert        
import Haskell.Hatchet.HsParsePostProcess
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)
import Haskell.Hatchet.HsSyn             (HsDecl)

emptySign :: ModuleInfo
emptySign = emptyModuleInfo

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

instance Eq ModuleInfo where
  m1 == m2 = 
      (varAssumps m1, dconsAssumps m1, 
       classHierarchy m1, tyconsMembers m1, infixDecls m1,
       synonyms m1) == (varAssumps m2, dconsAssumps m2, 
       classHierarchy m2, tyconsMembers m2, infixDecls m2,
       synonyms m2)

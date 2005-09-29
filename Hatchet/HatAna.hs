{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

todo:
     - write difference function for ModuleInfos
     - include Prelude (or undefined) during type inference

-}

module Hatchet.HatAna where

import Common.AS_Annotation 

import Hatchet.HaskellUtils              (extractSentences)
import Hatchet.ExtHaskellCvrt            

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
                                          joinModuleInfo,
                                          getTyconsMembers,
                                          getInfixDecls)
import Haskell.Hatchet.TIHetsModule      (tiModule)
import Haskell.Hatchet.AnnotatedHsSyn    
import Haskell.Hatchet.SynConvert        
import Haskell.Hatchet.HsParsePostProcess
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)
import Haskell.Hatchet.HsSyn             (HsDecl)
import Haskell.Hatchet.TIPhase

import Data.List ((\\))
import Data.FiniteMap (minusFM)

hatAna :: [HsDecl] -> ModuleInfo -> (ModuleInfo, [Named AHsDecl])
hatAna = hatAna2 preludeModInfo 

hatAna2 :: ModuleInfo -> [HsDecl] -> ModuleInfo 
        -> (ModuleInfo, [Named AHsDecl])
hatAna2 prelude hs sig = 
    let ahs = map toAHsDecl $ fixFunBinds $ cvrtHsDeclList hs
        aMod = AHsModule (moduleName sig) Nothing [] ahs
        (moduleEnv,
         dataConEnv,
         newClassHierarchy,
         newKindInfoTable,
         moduleRenamed,
         moduleSynonyms) = tiModule aMod (joinModuleInfo sig prelude)
        modInfo = sig {     varAssumps = moduleEnv, 
                            dconsAssumps = dataConEnv, 
                            classHierarchy = newClassHierarchy,
                            kinds = newKindInfoTable,
                            tyconsMembers = getTyconsMembers moduleRenamed,
                            infixDecls = getInfixDecls moduleRenamed,
                            synonyms = moduleSynonyms }
        in (diffModInfo modInfo prelude, extractSentences moduleRenamed)

instance Eq ModuleInfo where
  m1 == m2 = 
      (varAssumps m1, dconsAssumps m1, 
       classHierarchy m1, tyconsMembers m1, infixDecls m1,
       synonyms m1) == (varAssumps m2, dconsAssumps m2, 
       classHierarchy m2, tyconsMembers m2, infixDecls m2,
       synonyms m2)

diffModInfo :: ModuleInfo -> ModuleInfo -> ModuleInfo
diffModInfo mod1 mod2
    = ModuleInfo {
            moduleName = AModule mn,
            varAssumps = comb varAssumps minusFM,
            dconsAssumps = comb dconsAssumps minusFM,
            kinds = comb kinds minusFM,
            tyconsMembers = comb tyconsMembers (\\),
            classHierarchy = comb classHierarchy minusFM,
            synonyms = comb synonyms (\\),
            infixDecls = comb infixDecls (\\)
    }
    where comb field joiningMethod = joiningMethod (field mod1) (field mod2)
          mn = (\(AModule x) -> x) (moduleName mod1)


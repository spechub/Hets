{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   
   The comorphism functions for HasCASL2Haskell
-}

module ToHaskell.FromHasCASL where

import Common.AS_Annotation
import Common.Id

import HasCASL.Le

import ToHaskell.TranslateAna
import ToHaskell.TranslateId

import Haskell.Hatchet.MultiModuleBasics 
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.SynConvert
import Haskell.HatAna

mapSignature :: Env -> Maybe(ModuleInfo, [Named AHsDecl]) 
mapSignature sign = 
    let hs = translateAna sign
    in	Just(hatAna hs emptyModuleInfo) 

mapSentence :: Named Sentence -> [Named AHsDecl] 
mapSentence sen = case sentence sen of
    DatatypeSen dt -> map translateDt dt 
    _ -> []

translateDt :: DatatypeDefn -> Named AHsDecl
translateDt (DatatypeConstr i _ _ args alts) = 
   	 let hsname = HsIdent $ translateIdWithType UpperId i in
         NamedSen ("ga_" ++ showId i "") $
         toAHsDecl $ HsDataDecl (SrcLoc 0 0)
	               [] -- empty HsContext
	               hsname
		       (map getArg args) -- type arguments
		       (map translateAltDefn alts) -- [HsConDecl] 
		       [(UnQual $ HsIdent "Show")]

mapTheory :: (Env, [Named Sentence]) -> (ModuleInfo, [Named AHsDecl])
mapTheory (sign, csens) =
    let hs = translateAna sign
	(mi, hsens) = hatAna hs emptyModuleInfo
	in (mi, hsens ++ concatMap mapSentence csens)

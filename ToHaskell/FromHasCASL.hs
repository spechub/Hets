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

import HasCASL.Le
import HasCASL.Builtin

import Haskell.Hatchet.MultiModuleBasics 
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.SynConvert
import Haskell.HatAna

import ToHaskell.TranslateAna

mapSingleSentence :: Env -> Sentence -> Maybe AHsDecl
mapSingleSentence sign sen = 
    case translateSentence sign $ NamedSen "" sen of
    [s] -> Just $ toAHsDecl $ sentence s
    _ -> Nothing

mapTheory :: (Env, [Named Sentence]) -> (ModuleInfo, [Named AHsDecl])
mapTheory (sig, csens) =
    let sign = sig { typeMap = addUnit $ typeMap sig,
		     assumps = addOps $ assumps sig }
        hs = translateSig sign
	ps = concatMap (translateSentence sign) csens
	cs = cleanSig hs ps
        (mi, _) = hatAna (cs ++ map sentence ps) emptyModuleInfo
	in (mi, map ( \ s -> NamedSen "" $ toAHsDecl s) cs
	        ++ map (mapNamed toAHsDecl) ps)


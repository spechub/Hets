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

import ToHaskell.TranslateAna

import Haskell.Hatchet.MultiModuleBasics 
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.SynConvert
import Haskell.HatAna

mapSingleSentence :: Env -> Sentence -> Maybe AHsDecl
mapSingleSentence sign sen = 
    case translateSentence sign $ NamedSen "" sen of
    [s] -> Just $ toAHsDecl $ sentence s
    _ -> Nothing

mapTheory :: (Env, [Named Sentence]) -> (ModuleInfo, [Named AHsDecl])
mapTheory (sign, csens) =
    let hs = translateSig sign
	ps = concatMap (translateSentence sign) csens
        (mi, _) = hatAna (cleanSig hs ps ++ map sentence ps) emptyModuleInfo
	in (mi, map (mapNamed toAHsDecl) ps)


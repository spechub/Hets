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
import Common.GlobalAnnotations
import Common.Result

import HasCASL.Le
import HasCASL.AsToLe

import PNT
import PropPosSyntax hiding (ModuleName, Id, HsName)
import Haskell.HatAna
import Haskell.HatParser

import ToHaskell.TranslateAna


mapSingleSentence :: Env -> Sentence -> Maybe (HsDeclI PNT)
mapSingleSentence sign sen = Nothing
{-
    case translateSentence sign $ NamedSen "" sen of
    [s] -> Just $ toAHsDecl $ sentence s
    _ -> Nothing
-}

mapTheory :: (Env, [Named Sentence]) -> Maybe (Sign, [Named (HsDeclI PNT)])
mapTheory (sig, csens) = 
    let res@(Result _ m) = 
            hatAna (HsDecls $ translateSig sig, emptySign, emptyGlobalAnnos)
    in case m of 
              Nothing -> error $ show res
              Just (_, _, hs, sens) -> Just (hs, sens) 
{-
    let sign = addPreDefs sig 
        hs = translateSig sign
	ps = concatMap (translateSentence sign) csens
	fewHs = translateSig sig
	cs = cleanSig hs ps
	fewCs = cleanSig fewHs ps
        (mi, _) = hatAna2 myPrelude (cs ++ map sentence ps) emptyModuleInfo
	in (diffModInfo mi mi, map ( \ s -> NamedSen "" $ toAHsDecl s) fewCs
	    ++ map (mapNamed toAHsDecl) ps)

myPrelude :: ModuleInfo
myPrelude = ModuleInfo {
               moduleName = prelMod,
               varAssumps = (Env.listToEnv $ map assumpToPair myPreludeDefs),
               tyconsMembers = myTyconsMembers, 
               dconsAssumps = (Env.listToEnv $ map assumpToPair 
			       myPreludeDataCons),
               classHierarchy = Env.listToEnv [],
               kinds = (Env.listToEnv myPreludeTyconAndClassKinds),
               infixDecls = [],
               synonyms = []
              } where
	    myPreludeDefs =
		[mkPolyType (qual "undefined") $ TGen 0,
		 mkPolyType (qual "error") $ TArrow (TAp tList tChar) $ TGen 0]
	    prelMod = AModule "Prelude"
	    prel :: AHsIdentifier -> AHsName
	    prel = AQual prelMod
	    qual :: String -> AHsName
	    qual name = prel (AHsIdent name)
	    qUnit, qCons :: AHsName
	    qUnit = prel (AHsSpecial "()")
	    qCons = prel (AHsSymbol ":")
	    qNil = qual "[]"
	    qTrue = qual "True"
	    qFalse = qual "False"
	    qBool = qual "Bool"
	    qChar = qual "Char"
	    myTyconsMembers :: [(AHsName, [AHsName])]
	    myTyconsMembers
		= [(qBool, [qTrue, qFalse]),
		   (qUnit, [qUnit]),
		   (qNil, [qNil, qCons])]
	    mkTCon qn = TCon $ Tycon qn Star
	    tChar = mkTCon qChar
	    tUnit = mkTCon qUnit
	    tBool = mkTCon qBool
	    tList = TCon $ Tycon qNil $ Kfun Star Star
	    mkType l qn ty = qn :>: Forall l ([] :=> ty)
	    mkPolyType = mkType [Star]
	    mkMonoType = mkType []
	    pList = TAp tList $ TGen 0
	    nilCfun = mkPolyType qUnit pList
	    consCfun = mkPolyType qCons $ TArrow (TGen 0) $ TArrow pList pList
	    mkTBool = flip mkMonoType tBool
	    unitCfun = mkMonoType qUnit tUnit
	    falseCfun = mkTBool qFalse
	    trueCfun = mkTBool qTrue
	    myPreludeDataCons :: [Assump] 
	    myPreludeDataCons = [consCfun, nilCfun, unitCfun, 
				 trueCfun, falseCfun]
	    myPreludeTyconAndClassKinds :: [(AHsName, Kind)]
	    myPreludeTyconAndClassKinds
		=  (qNil, Star `Kfun` Star) : 
		   map ( \ i -> ( i, Star)) 
			   [qUnit, qBool, qChar, qual "Show"]
-}

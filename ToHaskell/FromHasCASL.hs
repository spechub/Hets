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
import HasCASL.AsToLe

import Haskell.Hatchet.Type
import Haskell.Hatchet.Representation
import qualified Haskell.Hatchet.Env as Env 
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

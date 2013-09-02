{- |
Module      :  $Header$
Description :  Static QVTR analysis
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module QVTR.StatAna where

import QVTR.As
import QVTR.Sign

import qualified CSMOF.As as CSMOFAs
import qualified CSMOF.Sign as CSMOFSign
import qualified CSMOF.StatAna as CSMOFStatAna

import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.AS_Annotation

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

basicAna :: (Transformation, Sign, GlobalAnnos) -> Result (Transformation, ExtSign Sign (), [Named Sen])
basicAna (trans, _, _) = 
  let 
    (sign,diagSign) = buildSignature trans
    (sen,diagSen) = buildSentences sign trans
  in Result (reverse diagSign ++ reverse diagSen)
            $ Just (trans, mkExtSign sign, sen)


buildSignature :: Transformation -> (Sign,[Diagnosis])
buildSignature (Transformation _ souMet tarMet _ rels) = 
  let 
    souMetSign = CSMOFStatAna.buildSignature (third souMet)
    tarMetSign = CSMOFStatAna.buildSignature (third tarMet)
    (relat,diagn) = buildRelations souMetSign tarMetSign rels
  in
    (Sign { sourceSign = souMetSign
         , targetSign = tarMetSign
         , nonTopRelations = fst relat
         , topRelations = snd relat
         }
     , diagn)


buildRelations :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Relation] -> ((Map.Map String RuleDef,Map.Map String RuleDef),[Diagnosis])
buildRelations souMetSign tarMetSign rels = 
  let 
    (nonTopRel,topRel) = separateTopFromNonTop rels
    calledTopRules = map (createCalledTopRule) topRel
    (nonTopRuleDef,diagn1) = foldr (createRuleDef souMetSign tarMetSign) (Map.empty,[]) (nonTopRel ++ calledTopRules)
    (topRuleDef,diagn2) = foldr (createRuleDef souMetSign tarMetSign) (Map.empty,[]) topRel
  in
    ((nonTopRuleDef,topRuleDef), diagn1 ++ diagn2)


separateTopFromNonTop :: [Relation] -> ([Relation],[Relation])
separateTopFromNonTop rels = 
  case rels of
    [] -> ([],[])
    r : rest -> let result = separateTopFromNonTop rest
                in
                  if isTop r then
                    (fst result,r : snd result)
                  else (r : fst result,snd result)


isTop :: Relation -> Bool
isTop (Relation top _ _ _ _ _ _ _) = top


createRuleDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Relation -> 
                   (Map.Map String RuleDef,[Diagnosis]) -> (Map.Map String RuleDef,[Diagnosis])
createRuleDef souMetSign tarMetSign (Relation top relN _ primD souD tarD _ _) (mapRD,diag) = 
  let (varTyp,diag2) = getTypesFromVars souMetSign tarMetSign primD souD tarD
      relName = if top then "Top_" ++ relN else relN
  in
    case Map.lookup relName mapRD of
      Nothing -> (Map.insert relName (RuleDef relName top varTyp) mapRD, diag ++ diag2)
      Just r -> (mapRD, (mkDiag Error "rule names must be unique" (QVTR.Sign.name r)) : (diag ++ diag2))


-- Generate rule parameters from primitive domains, source and target object domains
getTypesFromVars :: CSMOFSign.Sign -> CSMOFSign.Sign -> [PrimitiveDomain] -> Domain -> Domain -> ([CSMOFSign.TypeClass],[Diagnosis])
getTypesFromVars souMetSign tarMetSign primD souD tarD = 
  let 
    (souDomObj,d1) = getDomainType souMetSign souD
    (tarDomObj,d2) = getDomainType tarMetSign tarD
    (pTypes,d3) = unzip $ map (getPrimitiveDomainType souMetSign tarMetSign) primD
    primTypes = getSomething pTypes
  in 
    case souDomObj of
      Nothing -> case tarDomObj of
                   Nothing -> (primTypes, d1 ++ d2 ++ (concat d3))
                   Just tDO -> (tDO : primTypes, d1 ++ d2 ++ (concat d3))
      Just sDO -> case tarDomObj of
                   Nothing -> (sDO : primTypes, d1 ++ d2 ++ (concat d3))
                   Just tDO -> (sDO : (tDO : primTypes), d1 ++ d2 ++ (concat d3))


getDomainType :: CSMOFSign.Sign -> Domain -> (Maybe CSMOFSign.TypeClass,[Diagnosis])
getDomainType metSign (Domain _ (ObjectTemplate _ _ dType _)) = getType (Set.toList (CSMOFSign.types metSign)) dType


getPrimitiveDomainType :: CSMOFSign.Sign -> CSMOFSign.Sign -> PrimitiveDomain -> (Maybe CSMOFSign.TypeClass,[Diagnosis])
getPrimitiveDomainType souMetSign tarMetSign (PrimitiveDomain _ primType) = 
  let (typ,diag) = getType (Set.toList (CSMOFSign.types souMetSign)) primType
  in
    case typ of
      Nothing -> let (typ2,diag2) = getType (Set.toList (CSMOFSign.types tarMetSign)) primType
                 in (typ2, diag ++ diag2)
      Just el -> (Just el, diag)


getType :: [CSMOFSign.TypeClass] -> String -> (Maybe CSMOFSign.TypeClass,[Diagnosis])
getType types dType = 
  case types of
    [] -> (Nothing, [(mkDiag Error "type not found" dType)])
    typ : rest -> if CSMOFSign.name typ == dType then (Just typ,[])
                  else getType rest dType


getSomething :: [Maybe CSMOFSign.TypeClass] -> [CSMOFSign.TypeClass] 
getSomething list = 
  case list of
    [] -> []
    el : rest -> case el of
                   Nothing -> getSomething rest
                   Just typ -> typ : getSomething rest

  
-- Creates a non-top version of a top rule in order to generate a parametrized version of itself
createCalledTopRule :: Relation -> Relation
createCalledTopRule (Relation top a b c d e f g) = (Relation (not top) a b c d e f g)



buildSentences :: Sign -> Transformation -> ([Named Sen],[Diagnosis])
buildSentences sign (Transformation _ souMet tarMet kes rels) =
  let 
    (_, sMetN, _) = souMet
    (_, tMetN, _) = tarMet
    (keyConstr,diag) = buildKeyConstr sign sMetN tMetN kes
    (qvtRules,diag2) = ([],[]) -- buildRules rels
  in
    (keyConstr ++ qvtRules, diag ++ diag2)


buildKeyConstr :: Sign -> String -> String -> [Key] -> ([Named Sen],[Diagnosis])
buildKeyConstr _ _ _ [] = ([],[])
buildKeyConstr sign sMetN tMetN (k : rest) = 
  let 
    (restK,diag) = buildKeyConstr sign sMetN tMetN rest
    (ke,diag2) = buildKeyC sign sMetN tMetN k
  in 
    case ke of
      Nothing -> (restK, diag ++ diag2)
      Just el -> (el :  restK, diag ++ diag2)


buildKeyC :: Sign -> String -> String -> Key -> (Maybe (Named Sen),[Diagnosis])
buildKeyC sign sMetN tMetN k = 
  if sMetN == (metamodel k) || tMetN == (metamodel k) then
    let (typ,diag) = getType (Set.toList (CSMOFSign.types (sourceSign sign))) (typeName k)
    in
      case typ of
        Nothing -> let (typ2,diag2) = getType (Set.toList (CSMOFSign.types (targetSign sign))) (typeName k)
                   in
                     case typ2 of
                       Nothing -> (Nothing, (mkDiag Error "type not found" (typeName k)) : (diag ++ diag2))
                       Just el -> if propKeysCheckOK (targetSign sign) (typeName k) (properties k) then 
                                    (Just (makeNamed "" (KeyConstr { keyConst = k })), diag ++ diag2)
                                  else (Nothing, (mkDiag Error "property not found" (properties k)) : (diag ++ diag2))
        Just el -> if propKeysCheckOK (sourceSign sign) (typeName k) (properties k) then 
                     (Just (makeNamed "" (KeyConstr { keyConst = k })), diag)
                   else (Nothing, (mkDiag Error "property not found" (properties k)) : diag)
  else (Nothing, [(mkDiag Error "metamodel does not exist" (sMetN ++ "-" ++ tMetN))])


propKeysCheckOK :: CSMOFSign.Sign -> String -> [PropKey] -> Bool
propKeysCheckOK metSign kType [] = True
propKeysCheckOK metSign kType (ke : rest) = (propKeyCheckOK metSign kType ke) && (propKeysCheckOK metSign kType rest)


propKeyCheckOK :: CSMOFSign.Sign -> String -> PropKey -> Bool
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (SimpleProp pName) = findProperty typRel props kType pName
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (OppositeProp oppPType oppPName) = findOppProperty typRel props kType oppPType oppPName


findProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> Bool
findProperty typRel props kType pName =
  let classes = kType : Set.toList (superClasses (Rel.map (CSMOFSign.name) typRel) kType)
  in findPropertyByTypeAndRole (Set.toList props) classes pName


findPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String -> Bool
findPropertyByTypeAndRole [] classes pName = False
findPropertyByTypeAndRole (p : rest) classes pName =
  if (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes && (CSMOFSign.targetRole p) == pName) || 
     (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes && (CSMOFSign.sourceRole p) == pName)
  then True
  else findPropertyByTypeAndRole rest classes pName


superClasses :: Rel.Rel String -> String -> Set.Set String
superClasses relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


findOppProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> String -> Bool
findOppProperty typRel props kType oppPType oppPName = 
  let classes = oppPType : Set.toList (superClasses (Rel.map (CSMOFSign.name) typRel) oppPType)
  in findOppPropertyByTypeAndRole (Set.toList props) classes oppPName kType


findOppPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String -> String -> Bool
findOppPropertyByTypeAndRole [] classes pName kType = False
findOppPropertyByTypeAndRole (p : rest) classes pName kType=
  if (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes && 
       (CSMOFSign.targetRole p) == pName && 
       (CSMOFSign.name (CSMOFSign.targetType p)) == kType) || 
     (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes && 
       (CSMOFSign.sourceRole p) == pName && 
       (CSMOFSign.name (CSMOFSign.sourceType p)) == kType)
  then True
  else findOppPropertyByTypeAndRole rest classes pName kType


third :: (String,String,CSMOFAs.Metamodel) -> CSMOFAs.Metamodel
third (_, _, c) = c

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
basicAna (trans, _, _) = let sign = buildSignature trans
                         in return (trans, mkExtSign sign, buildSentences sign trans)


buildSignature :: Transformation -> Sign
buildSignature (Transformation _ souMet tarMet _ rels) = 
  let 
    souMetSign = CSMOFStatAna.buildSignature (third souMet)
    tarMetSign = CSMOFStatAna.buildSignature (third tarMet)
    relat = buildRelations souMetSign tarMetSign rels
  in
    Sign { sourceSign = souMetSign
         , targetSign = tarMetSign
         , nonTopRelations = fst relat
         , topRelations = snd relat
         }


buildRelations :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Relation] -> (Map.Map String RuleDef,Map.Map String RuleDef)
buildRelations souMetSign tarMetSign rels = 
  let 
    (nonTopRel,topRel) = separateTopFromNonTop rels
    calledTopRules = map (createCalledTopRule) topRel
    nonTopRuleDef = foldr (createRuleDef souMetSign tarMetSign) Map.empty (nonTopRel ++ calledTopRules)
    topRuleDef = foldr (createRuleDef souMetSign tarMetSign) Map.empty topRel
  in
    (nonTopRuleDef,topRuleDef)


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


createRuleDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Relation -> Map.Map String RuleDef -> Map.Map String RuleDef
createRuleDef souMetSign tarMetSign (Relation top relN _ primD souD tarD _ _) mapRD = 
  let varTyp = getTypesFromVars souMetSign tarMetSign primD souD tarD
      relName = if top then "Top_" ++ relN else relN
  in
    case Map.lookup relName mapRD of
      Nothing -> Map.insert relName (RuleDef relName top varTyp) mapRD
      Just r -> mapRD -- ERROR, rule names must be unique


-- Generate rule parameters from primitive domains, source and target object domains
getTypesFromVars :: CSMOFSign.Sign -> CSMOFSign.Sign -> [PrimitiveDomain] -> Domain -> Domain -> [CSMOFSign.TypeClass]
getTypesFromVars souMetSign tarMetSign primD souD tarD = 
  let 
    souDomObj = getDomainType souMetSign souD
    tarDomObj = getDomainType tarMetSign tarD
    pTypes = map (getPrimitiveDomainType souMetSign tarMetSign) primD
    primTypes = getSomething pTypes
  in 
    case souDomObj of
      Nothing -> case tarDomObj of
                   Nothing -> primTypes
                   Just tDO -> tDO : primTypes
      Just sDO -> case tarDomObj of
                   Nothing -> sDO : primTypes
                   Just tDO -> sDO : (tDO : primTypes)    


getDomainType :: CSMOFSign.Sign -> Domain -> Maybe CSMOFSign.TypeClass
getDomainType metSign (Domain _ (ObjectTemplate _ _ dType _)) = getType (Set.toList (CSMOFSign.types metSign)) dType


getPrimitiveDomainType :: CSMOFSign.Sign -> CSMOFSign.Sign -> PrimitiveDomain -> Maybe CSMOFSign.TypeClass
getPrimitiveDomainType souMetSign tarMetSign (PrimitiveDomain _ primType) = 
  case getType (Set.toList (CSMOFSign.types souMetSign)) primType of
    Nothing -> getType (Set.toList (CSMOFSign.types tarMetSign)) primType
    Just el -> Just el


getType :: [CSMOFSign.TypeClass] -> String -> Maybe CSMOFSign.TypeClass
getType types dType = 
  case types of
    [] -> Nothing -- ERROR, type not found
    typ : rest -> if CSMOFSign.name typ == dType then Just typ
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



buildSentences :: Sign -> Transformation -> [Named Sen]
buildSentences sign (Transformation _ souMet tarMet kes rels) =
  let 
    (_, sMetN, _) = souMet
    (_, tMetN, _) = tarMet
    keyConstr = buildKeyConstr sign sMetN tMetN kes
    qvtRules = [] -- buildRules rels
  in
    keyConstr ++ qvtRules


buildKeyConstr :: Sign -> String -> String -> [Key] -> [Named Sen]
buildKeyConstr _ _ _ [] = []
buildKeyConstr sign sMetN tMetN (k : rest) = 
  let 
    restK = buildKeyConstr sign sMetN tMetN rest
    ke = buildKeyC sign sMetN tMetN k
  in 
    case ke of
      Nothing -> restK
      Just el -> el :  restK


buildKeyC :: Sign -> String -> String -> Key -> Maybe (Named Sen)
buildKeyC sign sMetN tMetN k = 
  if sMetN == (metamodel k) || tMetN == (metamodel k) then
    case getType (Set.toList (CSMOFSign.types (sourceSign sign))) (typeName k) of
      Nothing -> case getType (Set.toList (CSMOFSign.types (targetSign sign))) (typeName k) of
                   Nothing -> Nothing -- ERROR, the type does not exist within the metamodel
                   Just el -> if propKeysCheckOK (targetSign sign) (typeName k) (properties k) then 
                                Just (makeNamed "" (KeyConstr { keyConst = k })) 
                              else Nothing -- ERROR, properties are not within the corresponding type
      Just el -> if propKeysCheckOK (sourceSign sign) (typeName k) (properties k) then 
                   Just (makeNamed "" (KeyConstr { keyConst = k })) 
                 else Nothing -- ERROR, properties are not within the corresponding type
  else Nothing -- ERROR, metamodel does not exist


propKeysCheckOK :: CSMOFSign.Sign -> String -> [PropKey] -> Bool
propKeysCheckOK metSign kType [] = True
propKeysCheckOK metSign kType (ke : rest) = (propKeyCheckOK metSign kType ke) && (propKeysCheckOK metSign kType rest)


propKeyCheckOK :: CSMOFSign.Sign -> String -> PropKey -> Bool
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (SimpleProp pName) = findProperty typRel props kType pName
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (OppositeProp oppPType oppPName) = findOppProperty typRel props kType oppPType oppPName


findProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> Bool
findProperty typRel props kType pName = True
--  let propSuper = getPropsInHierarchy typRel kType
--  in findPropertyByTypeAndRole ((Set.toList props) ++ propSuper) kType pName


--findPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> String -> String -> Bool
--findPropertyByTypeAndRole [] kType pName = False
--findPropertyByTypeAndRole (p : rest) kType pName =
--  if ((sourceType p) == kType && (targetRole p) == pName) || ((targetType p) == kType && (sourceRole p) == pName)
--  then True
--  else findPropertyByTypeAndRole rest kType pName


--getPropsInHierarchy :: Rel.Rel CSMOFSign.TypeClass -> String -> [CSMOFSign.PropertyT]
--getPropsInHierarchy typRel kType = 
--  let superC = Set.toList (superClasses (Rel.map (CSMOFSign.name) typRel) kType)
--  in map ((++) . ) superC


superClasses :: Rel.Rel String -> String -> Set.Set String
superClasses relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


findOppProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> String -> Bool
findOppProperty typRel props kType oppPType oppPName = True --ToDo tengo que buscar la propiedad con esta informacion



third :: (String,String,CSMOFAs.Metamodel) -> CSMOFAs.Metamodel
third (_, _, c) = c

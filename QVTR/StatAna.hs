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
buildSignature (Transformation _ souMet tarMet kS rels) = 
  let 
    souMetSign = CSMOFStatAna.buildSignature (third souMet)
    tarMetSign = CSMOFStatAna.buildSignature (third tarMet)
    (relat,diagn) = buildRelations souMetSign tarMetSign rels
    (keyD,diagn2) = buildKeyDefs souMetSign tarMetSign kS
  in
    (Sign { sourceSign = souMetSign
         , targetSign = tarMetSign
         , nonTopRelations = fst relat
         , topRelations = snd relat
         , keyDefs = keyD
         }
     , diagn ++ diagn2)


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
isTop (Relation tp _ _ _ _ _ _ _) = tp


createRuleDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Relation -> 
                   (Map.Map String RuleDef,[Diagnosis]) -> (Map.Map String RuleDef,[Diagnosis])
createRuleDef souMetSign tarMetSign (Relation tp relN _ prD souD tarD _ _) (mapRD,diag) = 
  let (varTyp,diag2) = getTypesFromVars souMetSign tarMetSign prD souD tarD
      rName = if tp then "Top_" ++ relN else relN
  in
    case Map.lookup rName mapRD of
      Nothing -> (Map.insert rName (RuleDef rName tp varTyp) mapRD, diag ++ diag2)
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
                   Just tDO -> (tDO : primTypes, concat d3)
      Just sDO -> case tarDomObj of
                   Nothing -> (sDO : primTypes, d1 ++ d2 ++ (concat d3))
                   Just tDO -> (sDO : (tDO : primTypes), concat d3)


getDomainType :: CSMOFSign.Sign -> Domain -> (Maybe CSMOFSign.TypeClass,[Diagnosis])
getDomainType metSign (Domain _ (ObjectTemplate _ _ dType _)) = getType (Set.toList (CSMOFSign.types metSign)) dType


getPrimitiveDomainType :: CSMOFSign.Sign -> CSMOFSign.Sign -> PrimitiveDomain -> (Maybe CSMOFSign.TypeClass,[Diagnosis])
getPrimitiveDomainType souMetSign tarMetSign (PrimitiveDomain _ prType) = 
  let (typ,diag) = getType (Set.toList (CSMOFSign.types souMetSign)) prType
  in
    case typ of
      Nothing -> let (typ2,diag2) = getType (Set.toList (CSMOFSign.types tarMetSign)) prType
                 in 
                   case typ2 of 
                     Nothing -> (typ2, diag ++ diag2)
                     Just _ -> (typ2, [])
      Just _ -> (typ, [])


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
createCalledTopRule (Relation tp a b c d e f g) = (Relation (not tp) a b c d e f g)


buildKeyDefs :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Key] -> ([(String,String)],[Diagnosis])
buildKeyDefs _ _ [] = ([],[])
buildKeyDefs souMet tarMet (k : rest) = 
  let (restK,diag) = buildKeyDefs souMet tarMet rest
      (ke,diag2) = buildKeyDef souMet tarMet k
  in 
    case ke of
      Nothing -> (restK, diag ++ diag2)
      Just el -> (el :  restK, diag ++ diag2)


buildKeyDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Key -> (Maybe (String,String),[Diagnosis])
buildKeyDef souMet tarMet k = 
  let (typ,diag) = getType (Set.toList (CSMOFSign.types souMet)) (typeName k)
  in
    case typ of
      Nothing -> let (typ2,diag2) = getType (Set.toList (CSMOFSign.types tarMet)) (typeName k)
                 in
                   case typ2 of
                     Nothing -> (Nothing, (mkDiag Error "type not found" (typeName k)) : (diag ++ diag2))
                     Just _ -> if propKeysCheckOK tarMet (typeName k) (properties k) then 
                                 (Just (metamodel k, typeName k), [])
                               else (Nothing, (mkDiag Error "property not found" (properties k)) : (diag ++ diag2))
      Just _ -> if propKeysCheckOK souMet (typeName k) (properties k) then 
                  (Just (metamodel k, typeName k), [])
                else (Nothing, (mkDiag Error "property not found" (properties k)) : diag)


-- Sentences

buildSentences :: Sign -> Transformation -> ([Named Sen],[Diagnosis])
buildSentences sign (Transformation _ souMet tarMet kes rels) =
  let 
    (_, sMetN, _) = souMet
    (_, tMetN, _) = tarMet
    (keyConstr,diag) = buildKeyConstr sign sMetN tMetN kes
    (qvtRules,diag2) = buildRules sign souMet tarMet rels
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
                       Just _ -> if propKeysCheckOK (targetSign sign) (typeName k) (properties k) then 
                                   (Just (makeNamed "" (KeyConstr { keyConst = k })), [])
                                 else (Nothing, (mkDiag Error "property not found" (properties k)) : (diag ++ diag2))
        Just _ -> if propKeysCheckOK (sourceSign sign) (typeName k) (properties k) then 
                    (Just (makeNamed "" (KeyConstr { keyConst = k })), [])
                  else (Nothing, (mkDiag Error "property not found" (properties k)) : diag)
  else (Nothing, [(mkDiag Error "metamodel does not exist" (sMetN ++ "-" ++ tMetN))])


propKeysCheckOK :: CSMOFSign.Sign -> String -> [PropKey] -> Bool
propKeysCheckOK _ _ [] = True
propKeysCheckOK metSign kType (ke : rest) = (propKeyCheckOK metSign kType ke) && (propKeysCheckOK metSign kType rest)


propKeyCheckOK :: CSMOFSign.Sign -> String -> PropKey -> Bool
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (SimpleProp pN) = findProperty typRel props kType pN
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (OppositeProp oppPType oppPName) = findOppProperty typRel props kType oppPType oppPName


findProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> Bool
findProperty typRel props kType pN =
  let classes = kType : Set.toList (superClasses (Rel.map (CSMOFSign.name) typRel) kType)
  in findPropertyByTypeAndRole (Set.toList props) classes pN


findPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String -> Bool
findPropertyByTypeAndRole [] _ _ = False
findPropertyByTypeAndRole (p : rest) classes pN =
  if (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes && (CSMOFSign.targetRole p) == pN) || 
     (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes && (CSMOFSign.sourceRole p) == pN)
  then True
  else findPropertyByTypeAndRole rest classes pN


superClasses :: Rel.Rel String -> String -> Set.Set String
superClasses relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


findOppProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT -> String -> String -> String -> Bool
findOppProperty typRel props kType oppPType oppPName = 
  let classes = oppPType : Set.toList (superClasses (Rel.map (CSMOFSign.name) typRel) oppPType)
  in findOppPropertyByTypeAndRole (Set.toList props) classes oppPName kType


findOppPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String -> String -> Bool
findOppPropertyByTypeAndRole [] _ _ _ = False
findOppPropertyByTypeAndRole (p : rest) classes pN kType=
  if (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes && 
       (CSMOFSign.targetRole p) == pN && 
       (CSMOFSign.name (CSMOFSign.targetType p)) == kType) || 
     (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes && 
       (CSMOFSign.sourceRole p) == pN && 
       (CSMOFSign.name (CSMOFSign.sourceType p)) == kType)
  then True
  else findOppPropertyByTypeAndRole rest classes pN kType


third :: (String,String,CSMOFAs.Metamodel) -> CSMOFAs.Metamodel
third (_, _, c) = c



buildRules :: Sign -> (String,String,CSMOFAs.Metamodel) -> (String,String,CSMOFAs.Metamodel) -> [Relation] -> ([Named Sen],[Diagnosis])
buildRules sign souMet tarMet rul = 
  let 
    diag = checkRules sign souMet tarMet rul
  in 
    ([makeNamed "" (QVTSen { rules = rul })], diag)


checkRules :: Sign -> (String,String,CSMOFAs.Metamodel) -> (String,String,CSMOFAs.Metamodel) -> [Relation] -> [Diagnosis]
checkRules _ _ _ [] = []
checkRules sign souMet tarMet (r : rest) = (checkRule sign souMet tarMet r) ++ (checkRules sign souMet tarMet rest)


checkRule :: Sign -> (String,String,CSMOFAs.Metamodel) -> (String,String,CSMOFAs.Metamodel) -> Relation -> [Diagnosis]
checkRule sign souMet tarMet (Relation tp relN varS prD souDom tarDom whenC whereC) = []
--  let 
--    (sMetID, sMetN, _) = souMet
--    (tMetID, tMetN, _) = tarMet

--              , relName :: String
--              , varSet :: [RelVar]
--              , primDomains :: [PrimitiveDomain]
--              , sourceDomain :: Domain
--              , targetDomain :: Domain
--              , whenCond :: Maybe WhenWhere
--              , whereCond :: Maybe WhenWhere
--              }

-- los tipos en RelVar existen
-- los tipos en PrimitiveDomain existen
-- los nombres de variables en RelVar, PrimitiveDomain, Domain no se repiten
-- el domModelId del source y target Domain son los de la transformacion
-- los domMeta del source (de todos los obj templ) es el del source de la trans. Idem para el target
-- los domType del source y target existen en el source y target meta, respectivamente
-- los pName son propiedades que existen en cada domType
-- no hago nada con las oclExpre
-- para cada RelInVok de un WhenWhere, el nombre de la regla existe
-- para cada RelInvok los parametros son variables definidas y tienen los tipos de la relacion


--ObjectTemplate
--domVar :: String
--domMeta :: String
--domType :: String
--templateList :: [PropertyTemplate]

--pName :: String
--oclExpre :: Maybe String
--objTemp :: Maybe ObjectTemplate



-- Get every ObjectTemplate from a Domain (recursive)
getObjectTemplates :: Domain -> [ObjectTemplate]
getObjectTemplates dom = (template dom) : (getObjectTemplatesFromOT (template dom))

getObjectTemplatesFromOT :: ObjectTemplate -> [ObjectTemplate]
getObjectTemplatesFromOT ot = 
  let otList = getOT $ templateList ot
  in foldr ((++) . getObjectTemplatesFromOT) [] otList

getOT :: [PropertyTemplate] -> [ObjectTemplate] 
getOT list = 
  case list of
    [] -> []
    el : rest -> case objTemp el of
                   Nothing -> getOT rest
                   Just typ -> typ : getOT rest




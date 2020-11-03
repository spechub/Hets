{- |
Module      :  ./QVTR/StatAna.hs
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

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

basicAna :: (Transformation, Sign, GlobalAnnos) ->
            Result (Transformation, ExtSign Sign (), [Named Sen])
basicAna (trans, _, _) =
  let
    (sign, diagSign) = buildSignature trans
    (sen, diagSen) = buildSentences sign trans
  in Result (reverse diagSign ++ reverse diagSen)
            $ Just (trans, mkExtSign sign, sen)


buildSignature :: Transformation -> (Sign, [Diagnosis])
buildSignature (Transformation _ souMet tarMet kS rels) =
  let
    souMetSign = CSMOFStatAna.buildSignature (third souMet)
    tarMetSign = CSMOFStatAna.buildSignature (third tarMet)
    (relat, diagn) = buildRelations souMetSign tarMetSign rels
    (keyD, diagn2) = buildKeyDefs souMetSign tarMetSign kS
  in
    (Sign { sourceSign = souMetSign
          , targetSign = tarMetSign
          , nonTopRelations = fst relat
          , topRelations = snd relat
          , keyDefs = keyD
          }
     , diagn ++ diagn2)


buildRelations :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Relation] ->
                  ((Map.HashMap String RuleDef, Map.HashMap String RuleDef), [Diagnosis])
buildRelations souMetSign tarMetSign rels =
  let
    (nonTopRel, topRel) = separateTopFromNonTop rels
    calledTopRules = map createCalledTopRule topRel
    (nonTopRuleDef, diagn1) = foldr (createRuleDef souMetSign tarMetSign)
                                    (Map.empty, []) (nonTopRel ++ calledTopRules)
    (topRuleDef, diagn2) = foldr (createRuleDef souMetSign tarMetSign)
                                 (Map.empty, []) topRel
  in
    ((nonTopRuleDef, topRuleDef), diagn1 ++ diagn2)


separateTopFromNonTop :: [Relation] -> ([Relation], [Relation])
separateTopFromNonTop rels =
  case rels of
    [] -> ([], [])
    r : rest -> let result = separateTopFromNonTop rest
                in
                  if isTop r then
                    (fst result, r : snd result)
                  else (r : fst result, snd result)


isTop :: Relation -> Bool
isTop (Relation tp _ _ _ _ _ _ _) = tp


createRuleDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Relation ->
                   (Map.HashMap String RuleDef, [Diagnosis]) ->
                   (Map.HashMap String RuleDef, [Diagnosis])
createRuleDef souMetSign tarMetSign (Relation tp rName _ prD souD tarD _ _)
                                    (mapRD, diag) =
  let (varTyp, diag2) = getTypesFromVars souMetSign tarMetSign prD souD tarD
  in
    if tp
    then case Map.lookup ("Top_" ++ rName) mapRD of
           Nothing -> (Map.insert ("Top_" ++ rName)
                      (RuleDef ("Top_" ++ rName) tp []) mapRD, diag ++ diag2)
           Just r -> (mapRD, mkDiag Error "rule names must be unique"
                              (QVTR.Sign.name r) : (diag ++ diag2))
    else case Map.lookup rName mapRD of
           Nothing -> (Map.insert rName (RuleDef rName tp varTyp) mapRD,
                       diag ++ diag2)
           Just r -> (mapRD, mkDiag Error "rule names must be unique"
                              (QVTR.Sign.name r) : (diag ++ diag2))


-- Generate rule parameters from primitive domains, source and target object domains
getTypesFromVars :: CSMOFSign.Sign -> CSMOFSign.Sign -> [PrimitiveDomain] ->
                    Domain -> Domain -> ([CSMOFSign.TypeClass], [Diagnosis])
getTypesFromVars souMetSign tarMetSign primD souD tarD =
  let
    (souDomObj, d1) = getDomainType souMetSign souD
    (tarDomObj, d2) = getDomainType tarMetSign tarD
    (pTypes, d3) = unzip $ map (getPrimitiveDomainType souMetSign tarMetSign) primD
    primTypes = getSomething pTypes
  in
    case souDomObj of
      Nothing -> case tarDomObj of
                   Nothing -> (primTypes, d1 ++ d2 ++ concat d3)
                   Just tDO -> (tDO : primTypes, concat d3)
      Just sDO -> case tarDomObj of
                   Nothing -> (sDO : primTypes, d1 ++ d2 ++ concat d3)
                   Just tDO -> (sDO : (tDO : primTypes), concat d3)


getDomainType :: CSMOFSign.Sign -> Domain -> (Maybe CSMOFSign.TypeClass, [Diagnosis])
getDomainType metSign (Domain _ (ObjectTemplate _ _ dType _)) =
  getType (Set.toList (CSMOFSign.types metSign)) dType


getPrimitiveDomainType :: CSMOFSign.Sign -> CSMOFSign.Sign -> PrimitiveDomain ->
                          (Maybe CSMOFSign.TypeClass, [Diagnosis])
getPrimitiveDomainType souMetSign tarMetSign (PrimitiveDomain _ prType) =
  let (typ, diag) = getType (Set.toList (CSMOFSign.types souMetSign)) prType
  in
    case typ of
      Nothing -> let (typ2, diag2) =
                      getType (Set.toList (CSMOFSign.types tarMetSign)) prType
                 in
                   case typ2 of
                     Nothing -> (typ2, diag ++ diag2)
                     Just _ -> (typ2, [])
      Just _ -> (typ, [])


getType :: [CSMOFSign.TypeClass] -> String -> (Maybe CSMOFSign.TypeClass, [Diagnosis])
getType types dType =
  case types of
    [] -> (Nothing, [mkDiag Error "type not found" dType])
    typ : rest -> if CSMOFSign.name typ == dType then (Just typ, [])
                  else getType rest dType


getSomething :: [Maybe a] -> [a]
getSomething list =
  case list of
    [] -> []
    el : rest -> case el of
                   Nothing -> getSomething rest
                   Just typ -> typ : getSomething rest


-- Creates a non-top version of a top rule in order to generate a parametrized version of itself
createCalledTopRule :: Relation -> Relation
createCalledTopRule (Relation tp a b c d e f g) = Relation (not tp) a b c d e f g


buildKeyDefs :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Key] -> ([(String, String)], [Diagnosis])
buildKeyDefs _ _ [] = ([], [])
buildKeyDefs souMet tarMet (k : rest) =
  let (restK, diag) = buildKeyDefs souMet tarMet rest
      (ke, diag2) = buildKeyDef souMet tarMet k
  in
    case ke of
      Nothing -> (restK, diag ++ diag2)
      Just el -> (el : restK, diag ++ diag2)


buildKeyDef :: CSMOFSign.Sign -> CSMOFSign.Sign -> Key ->
               (Maybe (String, String), [Diagnosis])
buildKeyDef souMet tarMet k =
  let (typ, diag) = getType (Set.toList (CSMOFSign.types souMet)) (typeName k)
  in
    case typ of
      Nothing -> let (typ2, diag2) = getType (Set.toList (CSMOFSign.types tarMet))
                                      (typeName k)
                 in
                   case typ2 of
                     Nothing ->
                      (Nothing, mkDiag Error "type not found" (typeName k) :
                                 (diag ++ diag2))
                     Just _ -> if propKeysCheckOK tarMet (typeName k)
                                  (properties k)
                               then (Just (metamodel k, typeName k), [])
                               else (Nothing, mkDiag Error "property not found"
                                     (properties k) : (diag ++ diag2))
      Just _ -> if propKeysCheckOK souMet (typeName k) (properties k) then
                  (Just (metamodel k, typeName k), [])
                else (Nothing, mkDiag Error "property not found"
                                (properties k) : diag)


-- ------ Sentences --------

buildSentences :: Sign -> Transformation -> ([Named Sen], [Diagnosis])
buildSentences sign (Transformation _ souMet tarMet kes rels) =
  let
    (_, sMetN, _) = souMet
    (_, tMetN, _) = tarMet
    (keyConstr, diag) = buildKeyConstr sign sMetN tMetN kes
    (qvtRules, diag2) = buildRules sign souMet tarMet rels
  in
    (keyConstr ++ qvtRules, diag ++ diag2)


buildKeyConstr :: Sign -> String -> String -> [Key] -> ([Named Sen], [Diagnosis])
buildKeyConstr _ _ _ [] = ([], [])
buildKeyConstr sign sMetN tMetN (k : rest) =
  let
    (restK, diag) = buildKeyConstr sign sMetN tMetN rest
    (ke, diag2) = buildKeyC sign sMetN tMetN k
  in
    case ke of
      Nothing -> (restK, diag ++ diag2)
      Just el -> (el : restK, diag ++ diag2)


buildKeyC :: Sign -> String -> String -> Key -> (Maybe (Named Sen), [Diagnosis])
buildKeyC sign sMetN tMetN k =
  if sMetN == metamodel k || tMetN == metamodel k then
    let (typ, diag) = getType
          (Set.toList (CSMOFSign.types (sourceSign sign))) (typeName k)
    in
      case typ of
        Nothing -> let (typ2, diag2) = getType (Set.toList (CSMOFSign.types
                                        (targetSign sign))) (typeName k)
                   in
                     case typ2 of
                       Nothing -> (Nothing, mkDiag Error "type not found"
                                   (typeName k) : (diag ++ diag2))
                       Just _ ->
                        if propKeysCheckOK (targetSign sign)
                              (typeName k) (properties k)
                        then (Just (makeNamed "" KeyConstr { keyConst = k }), [])
                        else (Nothing, mkDiag Error "property not found"
                                        (properties k) : (diag ++ diag2))
        Just _ -> if propKeysCheckOK (sourceSign sign) (typeName k) (properties k) then
                    (Just (makeNamed "" KeyConstr { keyConst = k }), [])
                  else (Nothing, mkDiag Error "property not found" (properties k) : diag)
  else (Nothing, [mkDiag Error "metamodel does not exist" (sMetN ++ "-" ++ tMetN)])


propKeysCheckOK :: CSMOFSign.Sign -> String -> [PropKey] -> Bool
propKeysCheckOK _ _ [] = True
propKeysCheckOK metSign kType (ke : rest) = propKeyCheckOK metSign kType ke &&
 propKeysCheckOK metSign kType rest

propKeyCheckOK :: CSMOFSign.Sign -> String -> PropKey -> Bool
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType (SimpleProp pN) =
  findProperty typRel props kType pN
propKeyCheckOK (CSMOFSign.Sign _ typRel _ _ props _ _) kType
               (OppositeProp oppPType oppPName) =
  findOppProperty typRel props kType oppPType oppPName


findProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT ->
                String -> String -> Bool
findProperty typRel props kType pN =
  let classes = kType : Set.toList (superClasses
                          (Rel.map CSMOFSign.name typRel) kType)
  in findPropertyByTypeAndRole (Set.toList props) classes pN


findPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String -> Bool
findPropertyByTypeAndRole [] _ _ = False
findPropertyByTypeAndRole (p : rest) classes pN =
 (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes &&
  CSMOFSign.targetRole p == pN) ||
 (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes &&
  CSMOFSign.sourceRole p == pN) ||
 findPropertyByTypeAndRole rest classes pN


superClasses :: Rel.Rel String -> String -> Set.Set String
superClasses relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


findPropertyInHierarchy :: Rel.Rel CSMOFSign.TypeClass ->
                           Set.Set CSMOFSign.PropertyT ->
                           String -> String -> Maybe CSMOFSign.PropertyT
findPropertyInHierarchy typRel props kType pN =
  let classes = kType : Set.toList (superClasses (Rel.map CSMOFSign.name typRel) kType)
  in findPropertyElemByTypeAndRole (Set.toList props) classes pN


findPropertyElemByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String ->
                                 Maybe CSMOFSign.PropertyT
findPropertyElemByTypeAndRole [] _ _ = Nothing
findPropertyElemByTypeAndRole (p : rest) classes pN =
  if (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes &&
      CSMOFSign.targetRole p == pN) ||
     (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes &&
      CSMOFSign.sourceRole p == pN)
  then Just p
  else findPropertyElemByTypeAndRole rest classes pN


findOppProperty :: Rel.Rel CSMOFSign.TypeClass -> Set.Set CSMOFSign.PropertyT ->
                  String -> String -> String -> Bool
findOppProperty typRel props kType oppPType oppPName =
  let classes = oppPType : Set.toList (superClasses (Rel.map CSMOFSign.name typRel)
                                        oppPType)
  in findOppPropertyByTypeAndRole (Set.toList props) classes oppPName kType


findOppPropertyByTypeAndRole :: [CSMOFSign.PropertyT] -> [String] -> String ->
                                String -> Bool
findOppPropertyByTypeAndRole [] _ _ _ = False
findOppPropertyByTypeAndRole (p : rest) classes pN kType =
 (elem (CSMOFSign.name (CSMOFSign.sourceType p)) classes &&
       CSMOFSign.targetRole p == pN &&
       CSMOFSign.name (CSMOFSign.targetType p) == kType) ||
 (elem (CSMOFSign.name (CSMOFSign.targetType p)) classes &&
       CSMOFSign.sourceRole p == pN &&
       CSMOFSign.name (CSMOFSign.sourceType p) == kType) ||
 findOppPropertyByTypeAndRole rest classes pN kType


getTargetType :: String -> CSMOFSign.PropertyT -> String
getTargetType pN p = CSMOFSign.name $
  if CSMOFSign.targetRole p == pN
  then CSMOFSign.targetType p
  else CSMOFSign.sourceType p


getOppositeType :: String -> CSMOFSign.PropertyT -> String
getOppositeType pN p = CSMOFSign.name $
  if CSMOFSign.sourceRole p == pN
  then CSMOFSign.targetType p
  else CSMOFSign.sourceType p


third :: (String, String, CSMOFAs.Metamodel) -> CSMOFAs.Metamodel
third (_, _, c) = c


buildRules :: Sign -> (String, String, CSMOFAs.Metamodel) ->
              (String, String, CSMOFAs.Metamodel) ->
              [Relation] -> ([Named Sen], [Diagnosis])
buildRules sign souMet tarMet rul =
  let
    (rel, diag) = checkRules sign souMet tarMet rul
  in (map (\ r -> makeNamed "" QVTSen { rule = r }) rel, diag)


checkRules :: Sign -> (String, String, CSMOFAs.Metamodel) ->
              (String, String, CSMOFAs.Metamodel) ->
              [Relation] -> ([RelationSen], [Diagnosis])
checkRules _ _ _ [] = ([], [])
checkRules sign souMet tarMet (r : rest) =
  let
    (rul, diag) = checkRule sign souMet tarMet r
    (restRul, restDiag) = checkRules sign souMet tarMet rest
  in
    (rul ++ restRul, diag ++ restDiag)


checkRule :: Sign -> (String, String, CSMOFAs.Metamodel) ->
             (String, String, CSMOFAs.Metamodel) -> Relation ->
             ([RelationSen], [Diagnosis])
checkRule sign _ _ (Relation tp rN vS prD souDom tarDom whenC whereC) =
  let
    rName = if tp then "Top_" ++ rN else rN

    (rDefNonTop, rDiagNonTop) = case Map.lookup rN (nonTopRelations sign) of
                            Nothing -> (RuleDef "" False [],
                             [mkDiag Error "non top relation not found" rName])
                            Just r -> (r, [])

    (rDef, rDiag) = if tp
                   then case Map.lookup rName (topRelations sign) of
                          Nothing -> (RuleDef "" False [],
                           [mkDiag Error "top relation not found" rName])
                          Just r -> (r, [])
                   else (RuleDef "" False [], [])

    pSet = collectParSet prD souDom tarDom
    vSet = collectVarSet vS prD souDom tarDom

    (souPat, diagSPat) = buildPattern souDom (sourceSign sign) vSet
    (tarPat, diagTPat) = buildPattern tarDom (targetSign sign) vSet
    (whenCl, diagW1Pat) = checkWhenWhere whenC
    (whereCl, diagW2Pat) = checkWhenWhere whereC

  in
    if tp
    then (RelationSen rDef vSet [] souPat tarPat whenCl whereCl : -- Top Rule
            [RelationSen rDefNonTop vSet pSet souPat tarPat whenCl whereCl], -- Non Top Rule
               rDiag ++ rDiagNonTop ++ diagSPat ++ diagTPat ++ diagW1Pat ++ diagW2Pat)
    else ([RelationSen rDefNonTop vSet pSet souPat tarPat whenCl whereCl],
            rDiag ++ rDiagNonTop ++ diagSPat ++ diagTPat ++ diagW1Pat ++ diagW2Pat)


collectParSet :: [PrimitiveDomain] -> Domain -> Domain -> [RelVar]
collectParSet prD souDom tarDom =
  let
    prDVS = collectPrimDomVarSet prD
    souVar = RelVar (domType $ template souDom) (domVar $ template souDom)
    tarVar = RelVar (domType $ template tarDom) (domVar $ template tarDom)
  in
    [souVar, tarVar] ++ prDVS


collectVarSet :: [RelVar] -> [PrimitiveDomain] -> Domain -> Domain -> [RelVar]
collectVarSet varS prD souDom tarDom =
  let
    souDomVS = collectDomainVarSet souDom
    tarDomVS = collectDomainVarSet tarDom
    prDVS = collectPrimDomVarSet prD
  in
    varS ++ prDVS ++ souDomVS ++ tarDomVS


collectPrimDomVarSet :: [PrimitiveDomain] -> [RelVar]
collectPrimDomVarSet = map (\ n -> RelVar (primType n) (primName n))


collectDomainVarSet :: Domain -> [RelVar]
collectDomainVarSet dom = collectRecursiveVars (Just $ template dom)


collectRecursiveVars :: Maybe ObjectTemplate -> [RelVar]
collectRecursiveVars Nothing = []
collectRecursiveVars (Just ot) =
  let otVar = RelVar (domType ot) (domVar ot)
  in
    otVar : foldr ((++) . collectRecursiveVars . objTemp) [] (templateList ot)


buildPattern :: Domain -> CSMOFSign.Sign -> [RelVar] -> (Pattern, [Diagnosis])
buildPattern dom sign vSet =
  let
    (patR, diag) = collectRecursiveRelInvoc (domVar (template dom))
     (domType (template dom)) (templateList (template dom)) sign vSet
    patPr = collectRecursivePreds vSet (Just $ template dom)
  in
    (Pattern (collectDomainVarSet dom) patR patPr, diag)


collectRecursiveRelInvoc :: String -> String -> [PropertyTemplate] ->
                            CSMOFSign.Sign -> [RelVar] ->
                            ([(CSMOFSign.PropertyT, RelVar, RelVar)],
                             [Diagnosis])
collectRecursiveRelInvoc _ _ [] _ _ = ([], [])
collectRecursiveRelInvoc nam typ (pt : restPT) sign vSet =
  case objTemp pt of
    Nothing -> ([], [])
    Just ot ->
      let
        prop = findPropertyInHierarchy (CSMOFSign.typeRel sign)
         (CSMOFSign.properties sign) typ (pName pt)
        (restProps, diagn) = collectRecursiveRelInvoc nam typ restPT sign vSet
        (recPr, recDiag) = collectRecursiveRelInvoc (domVar ot)
         (domType ot) (templateList ot) sign vSet
      in
        case prop of
          Nothing -> ([], mkDiag Error "property not found" pt :
                           (diagn ++ recDiag))
          Just p -> let
                      souV = RelVar typ nam
                      tarV = getVarFromTemplate pt vSet
                    in
                      case tarV of
                       Nothing -> (restProps ++ recPr, diagn ++ recDiag)
                        -- it is a OCL expression, not a variable
                       Just relVar -> ((p, souV, relVar) : (restProps ++ recPr),
                                        diagn ++ recDiag)


getVarFromTemplate :: PropertyTemplate -> [RelVar] -> Maybe RelVar
getVarFromTemplate (PropertyTemplate _ ocl _) relV =
  case ocl of
    Nothing -> Nothing
    Just (StringExp (VarExp v)) -> findVarFromName v relV
    _ -> Nothing


findVarFromName :: String -> [RelVar] -> Maybe RelVar
findVarFromName _ [] = Nothing
findVarFromName nam (v : restV) = if varName v == nam
                                  then Just v
                                  else findVarFromName nam restV


collectRecursivePreds :: [RelVar] -> Maybe ObjectTemplate ->
                         [(String, String, OCL)]
collectRecursivePreds _ Nothing = []
collectRecursivePreds vSet (Just ot) =
  let
    tList = templateList ot
    oclExps = foldr ((++) . getOclExpre (domVar ot) vSet) [] tList
  in
    oclExps ++ foldr ((++) . collectRecursivePreds vSet . objTemp) [] tList


getOclExpre :: String -> [RelVar] -> PropertyTemplate -> [(String, String, OCL)]
getOclExpre otN _ (PropertyTemplate pN ocl objT) =
  case ocl of
    Nothing -> case objT of
                 Nothing -> []
                 Just o -> [(pN, otN, StringExp (VarExp (domVar o)))]
                  -- ToDo Diagnosis
    Just s -> [(pN, otN, s)] -- ToDo Diagnosis


checkWhenWhere :: Maybe WhenWhere -> (Maybe WhenWhere, [Diagnosis])
checkWhenWhere ww = (ww, []) -- ToDo Diagnosis


{- ToDo :: Diagnosis
  las Keys no son vacias
  los tipos en RelVar existen
  los tipos en PrimitiveDomain existen
  los nombres de variables en RelVar, PrimitiveDomain, Domain no se repiten
  el domModelId del source y target Domain son los de la transformacion
  los domMeta del source (de todos los obj templ) es el del source de la trans. Idem para el target
  los domType del source y target existen en el source y target meta, respectivamente
  los pName son propiedades que existen en cada domType
  no hago nada con las oclExpre
  para cada RelInVok de un WhenWhere, el nombre de la regla existe
  para cada RelInvok los parametros son variables definidas y tienen los tipos de la relacion -}


-- Get every ObjectTemplate from a Domain (recursive)
getObjectTemplates :: Domain -> [ObjectTemplate]
getObjectTemplates dom = template dom : getObjectTemplatesFromOT (template dom)

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

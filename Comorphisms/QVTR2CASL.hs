{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Coding QVTR into CASL
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module Comorphisms.QVTR2CASL
    ( QVTR2CASL (..)
    ) where

import Logic.Logic
import Logic.Comorphism
import Common.DefaultMorphism

-- CSMOF
import qualified Comorphisms.CSMOF2CASL as CSMOF2CASL
import qualified CSMOF.Sign as CSMOF

-- QVTR
import QVTR.Logic_QVTR as QVTR
import QVTR.As as QVTRAs
import QVTR.Sign as QVTR
import QVTR.StatAna as QVTRAn

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL as C
import CASL.Sublogic
import CASL.Sign as C
import CASL.Morphism as C

import Common.AS_Annotation
import Common.ProofTree
import Common.Result
import Common.Id

import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set


-- | lid of the morphism
data QVTR2CASL = QVTR2CASL deriving Show

instance Language QVTR2CASL -- default is ok

instance Comorphism QVTR2CASL
    QVTR.QVTR
    ()
    QVTRAs.Transformation
    QVTR.Sen
    ()
    ()
    QVTR.Sign
    QVTR.Morphism
    ()
    ()
    ()
    CASL
    CASL_Sublogics
    CASLBasicSpec
    CASLFORMULA
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    CASLSign
    CASLMor
    C.Symbol
    C.RawSymbol
    ProofTree
    where
      sourceLogic QVTR2CASL = QVTR
      sourceSublogic QVTR2CASL = ()
      targetLogic QVTR2CASL = CASL
      mapSublogic QVTR2CASL _ = Just $ caslTop
        { has_part = False
        , sub_features = LocFilSub
        , cons_features = SortGen True True }
      map_theory QVTR2CASL = mapTheory
      map_sentence QVTR2CASL s = return . mapSen s (mapSign s)
      map_morphism QVTR2CASL = mapMor
      -- map_symbol QVTR2CASL _ = Set.singleton . mapSym
      is_model_transportable QVTR2CASL = True
      has_model_expansion QVTR2CASL = True
      is_weakly_amalgamable QVTR2CASL = True
      isInclusionComorphism QVTR2CASL = True


mapTheory :: (QVTR.Sign, [Named QVTR.Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = let cs = mapSign s in
  return (cs, map (mapNamed $ mapSen s cs) ns ++ sentences cs)


--TODO: 
--      generar free type de strings con ::, strings de source, target y transformacion
--      evitar sort String repetido en la signatura unificada
--      generar tambien signatura para BOOL
--      generar operacion ++ para concatenar strings

mapSign :: QVTR.Sign -> CASLSign
mapSign s = 
  let 
    sSign = CSMOF2CASL.mapSign (sourceSign s)
    tSign = CSMOF2CASL.mapSign (targetSign s)
    sUnion = C.uniteCASLSign sSign tSign
    relsProp = getPropertiesFromRelations (nonTopRelations s) (topRelations s)
    keysProp = getPropertiesFromKeys (keyDefs s)
    everyProp = (C.addMapSet (C.predMap sUnion) (C.addMapSet relsProp keysProp))
  in
    replacePredMap sUnion everyProp


getPropertiesFromRelations :: Map.Map String RuleDef ->  Map.Map String RuleDef -> PredMap
getPropertiesFromRelations nonTopRel topRel = getRelDef $ (Map.assocs nonTopRel) ++ (Map.assocs topRel)


getRelDef :: [(String,RuleDef)] -> PredMap
getRelDef [] = MapSet.empty
getRelDef ((nam,rulDef) : rest) = 
  let na = stringToId $ nam
      pa = foldr ((:) . stringToId . CSMOF.name) [] (QVTR.parameters rulDef)
  in MapSet.insert na (C.PredType pa) (getRelDef rest)


getPropertiesFromKeys :: [(String,String)] -> PredMap
getPropertiesFromKeys [] = MapSet.empty
getPropertiesFromKeys ((met,typ) : rest) = 
  MapSet.insert (predKeyName met typ) (C.PredType []) (getPropertiesFromKeys rest)


predKeyName :: String -> String -> Id
predKeyName met typ = stringToId $ "key_" ++ met ++ "_" ++ typ


replacePredMap :: CASLSign -> PredMap -> CASLSign
replacePredMap (C.Sign sR rSR eSR oM aO _ vM s dS eD aM gA eI) predM = (C.Sign sR rSR eSR oM aO predM vM s dS eD aM gA eI)


-- TODO:
--       generar sort constraint con free type de operaciones String
--       incluir restriccion de que es ++ en relacion a ::

mapSen :: QVTR.Sign -> CASLSign -> QVTR.Sen -> CASLFORMULA
mapSen qvtrSign _ (KeyConstr k) = createKeyFormula qvtrSign k
mapSen qvtrSign sig (QVTSen r) = createRuleFormula qvtrSign sig r


createKeyFormula :: QVTR.Sign -> Key-> CASLFORMULA
createKeyFormula qvtrSign k = 
  let 
    souVars = CSMOF2CASL.generateVars "x" 2
    tarVars = CSMOF2CASL.generateVars "y" $ toInteger $ length $ properties k
    typeSouVar = stringToId (typeName k)
    souVarDec = Var_decl souVars typeSouVar nullRange
    (tarVarDec,props) = getVarFromKey qvtrSign tarVars (properties k) (typeName k)
    pname = predKeyName (metamodel k) (typeName k)
    equal = Negation (Equation (Qual_var (head souVars) typeSouVar nullRange) 
                               Strong 
                               (Qual_var (head $ tail souVars) typeSouVar nullRange) 
                               nullRange)
                     nullRange
    sent = C.Relation equal
                      Implication 
                      (C.Relation 
                         (Junction Con (getPredicatesInvocation (mkSimpleId "x_1") (typeName k) tarVars (properties k) props) 
                                   nullRange) 
                         Implication 
                         (Junction Dis (map (\f -> Negation f nullRange) 
                                       (getPredicatesInvocation (mkSimpleId "x_2") (typeName k) tarVars (properties k) props))
                                   nullRange) 
                         nullRange)
                      nullRange
  in
    C.Relation 
      (C.Predication (C.Qual_pred_name pname (Pred_type [] nullRange) nullRange) 
                     []
                     nullRange) 
      C.Equivalence 
      (Quantification Universal (souVarDec : tarVarDec) sent nullRange) 
      nullRange


getPredicatesInvocation :: VAR -> String -> [VAR] -> [PropKey] -> [Maybe CSMOF.PropertyT] -> [CASLFORMULA]
getPredicatesInvocation _ _ [] [] [] = []
getPredicatesInvocation x typN (v : restV) (p : restP) (pT : restPT) =  
  let pr = case pT of
             Nothing -> trueForm
             Just prop -> case p of
                            SimpleProp pN -> let sor = QVTRAn.getOppositeType pN prop
                                                 sor2 = QVTRAn.getTargetType pN prop
                                             in Predication 
                                                  (C.Qual_pred_name (stringToId pN) 
                                                     (Pred_type [(stringToId sor),(stringToId sor2)] nullRange) 
                                                     nullRange) 
                                                  ((Qual_var x (stringToId typN) nullRange) :
                                                     [Qual_var v (stringToId sor2) nullRange]) 
                                                  nullRange
                            OppositeProp oPType oPName -> let sor = QVTRAn.getTargetType oPName prop
                                                          in
                                                           Predication 
                                                            (C.Qual_pred_name (stringToId oPName) 
                                                               (Pred_type [(stringToId oPType),(stringToId sor)] nullRange) 
                                                               nullRange) 
                                                            ((Qual_var v (stringToId oPType) nullRange) :
                                                               [Qual_var x (stringToId typN) nullRange]) 
                                                            nullRange
  in pr : getPredicatesInvocation x typN restV restP restPT
getPredicatesInvocation _ _ _ _ _ = []


getVarFromKey :: QVTR.Sign -> [VAR] -> [PropKey] -> String -> ([VAR_DECL], [Maybe CSMOF.PropertyT])
getVarFromKey _ [] [] _ = ([],[])
getVarFromKey qvtrSign (v : restV) (p : restP) typN = 
  let
    (decl,prop) = case p of
                    SimpleProp pN -> let (idP,propT) = getSortOfProperty qvtrSign typN pN
                                     in (Var_decl [v] idP nullRange, propT)
                    OppositeProp oPType oPName -> let (_,propT) = getSortOfProperty qvtrSign oPType oPName
                                                  in (Var_decl [v] (stringToId oPType) nullRange, propT)
    (restD,restPr) = getVarFromKey qvtrSign restV restP typN
  in
    (decl : restD, prop : restPr)
getVarFromKey _ _ _ _ = ([],[])


getSortOfProperty :: QVTR.Sign -> String -> String -> (Id, Maybe CSMOF.PropertyT)
getSortOfProperty qvtrSign typN pN = 
  let sourceProp = QVTRAn.findPropertyInHierarchy (CSMOF.typeRel $ QVTR.sourceSign qvtrSign) 
                                                  (CSMOF.properties $ QVTR.sourceSign qvtrSign) typN pN
      targetProp = QVTRAn.findPropertyInHierarchy (CSMOF.typeRel $ QVTR.targetSign qvtrSign) 
                                                  (CSMOF.properties $ QVTR.targetSign qvtrSign) typN pN
  in
    case sourceProp of
      Nothing -> case targetProp of
                   Nothing -> (stringToId "", Nothing)
                   Just p -> (stringToId $ QVTRAn.getTargetType pN p, Just p)
      Just p -> (stringToId $ QVTRAn.getTargetType pN p, Just p)


createRuleFormula :: QVTR.Sign -> CASLSign -> QVTR.RelationSen -> CASLFORMULA
createRuleFormula _ _ (QVTR.RelationSen rDef varS parS souPat tarPat whenC whereC) = 
  let
    rName = QVTR.name rDef
    parTyp = map (stringToId . varType) (parS)

    whenVarSet = collectWhenVarSet varS whenC
    souDomVarSet = Set.fromList (QVTR.patVarSet souPat)
    varSet_2 = Set.difference (Set.difference (Set.fromList (QVTR.patVarSet tarPat)) (Set.fromList whenVarSet)) souDomVarSet

  in C.Relation 
      (C.Predication (C.Qual_pred_name (stringToId rName) (Pred_type parTyp nullRange) nullRange) 
                     (createVarRule parS)
                     nullRange) 
      C.Equivalence 
      (if null whenVarSet
       then buildEmptyWhenFormula parS varS varSet_2 souPat tarPat whereC
       else buildNonEmptyWhenFormula whenVarSet parS varS varSet_2 souPat tarPat whenC whereC)
      nullRange


createVarRule :: [RelVar] -> [C.CASLTERM]
createVarRule [] = []
createVarRule (v : restV) = (Qual_var (mkSimpleId $ varName v) (stringToId $ varType v) nullRange) : createVarRule restV


collectWhenVarSet :: [RelVar] -> Maybe QVTRAs.WhenWhere -> [RelVar]
collectWhenVarSet _ Nothing = []
collectWhenVarSet varS (Just (WhenWhere relInv oclExp)) = 
  let 
    relVars = QVTRAn.getSomething $ map ((findRelVarFromName varS) . QVTRAs.name) relInv
    oclExpVars = foldr ((++) . (getVarIdsFromOCLExpre varS)) [] oclExp
  in
    relVars ++ oclExpVars


findRelVarFromName :: [RelVar] -> String -> Maybe RelVar
findRelVarFromName [] _ = Nothing
findRelVarFromName (v : restV) nam = if QVTRAs.varName v == nam 
                                     then Just v
                                     else findRelVarFromName restV nam


getVarIdsFromOCLExpre :: [RelVar] -> QVTRAs.OCL -> [RelVar]
getVarIdsFromOCLExpre varS (OCLExpre (VarExp v)) = case findRelVarFromName varS v of
                                                     Nothing -> []
                                                     Just r -> [r]
getVarIdsFromOCLExpre _ _ = []


-- 1. WhenVarSet = ∅
-- ∀ x1 , ..., xn ∈ (VarSet\2_VarSet)\ParSet, 
--      (Pattern1 → ∃ y1 , ..., ym ∈ 2_VarSet\ParSet, (Pattern2 ∧ where))

buildEmptyWhenFormula :: [RelVar] -> [RelVar] -> Set.Set RelVar -> Pattern -> Pattern -> Maybe WhenWhere -> CASLFORMULA
buildEmptyWhenFormula parS varS varSet_2 souPat tarPat whereC =
  let
    listPars = Set.fromList parS
    diffVarSet_1 = Set.toList $ Set.difference (Set.difference (Set.fromList varS) varSet_2) listPars
    diffVarSet_2 = Set.toList $ Set.difference varSet_2 listPars
    souPatF = buildPatternFormula souPat
    tarPatF = buildPatternFormula tarPat
    whereF = buildWhenWhereFormula whereC varS

    fst_sen = if whereF == trueForm
              then if tarPatF == trueForm
                   then if null diffVarSet_2
                        then trueForm
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_2)
                                              trueForm
                                              nullRange
                   else if null diffVarSet_2
                        then tarPatF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_2)
                                              tarPatF
                                              nullRange
              else if tarPatF == trueForm
                   then if null diffVarSet_2
                        then whereF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_2)
                                              whereF
                                              nullRange
                   else if null diffVarSet_2
                        then C.Junction Con [tarPatF,whereF] nullRange
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_2)
                                              (C.Junction Con [tarPatF,whereF] nullRange)
                                              nullRange


  in 
    if null diffVarSet_1
    then C.Relation souPatF Implication fst_sen nullRange
    else C.Quantification Universal 
                          (varDeclFromRelVar diffVarSet_1)
                          (C.Relation souPatF
                                      Implication 
                                      fst_sen
                                      nullRange)
                          nullRange


varDeclFromRelVar :: [RelVar] -> [VAR_DECL]
varDeclFromRelVar [] = []
varDeclFromRelVar (v : restV) = (Var_decl [mkSimpleId $ varName v] (stringToId $ varType v) nullRange) : varDeclFromRelVar restV


-- 2. WhenVarSet <> ∅
-- ∀ z1 , ..., zo ∈ WhenVarSet\ParSet, (when →
--      ∀ x1 , ..., xn ∈ (VarSet\(WhenVarSet ∪ 2_VarSet))\ParSet, (Pattern1 →
--            ∃ y1 , ..., ym ∈ 2_VarSet\ParSet, (Pattern2 ∧ where)))

buildNonEmptyWhenFormula :: [RelVar] -> [RelVar] -> [RelVar] -> Set.Set RelVar 
                                     -> Pattern -> Pattern -> Maybe WhenWhere -> Maybe WhenWhere -> CASLFORMULA
buildNonEmptyWhenFormula whenVarSet parS varS varSet_2 souPat tarPat whenC whereC =
  let
    listWhenVars = Set.fromList whenVarSet
    listPars = Set.fromList parS
    diffVarSet_1 = Set.toList $ Set.difference listWhenVars listPars
    diffVarSet_2 = Set.toList $ Set.difference (Set.difference (Set.fromList varS) (Set.union listWhenVars varSet_2)) listPars
    diffVarSet_3 = Set.toList $ Set.difference varSet_2 listPars
    souPatF = buildPatternFormula souPat
    tarPatF = buildPatternFormula tarPat
    whenF = buildWhenWhereFormula whenC varS
    whereF = buildWhenWhereFormula whereC varS

    snd_sen = if whereF == trueForm
              then if tarPatF == trueForm
                   then if null diffVarSet_3
                        then trueForm
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_3)
                                              trueForm
                                              nullRange
                   else if null diffVarSet_3
                        then tarPatF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_3)
                                              tarPatF
                                              nullRange
              else if tarPatF == trueForm
                   then if null diffVarSet_3
                        then whereF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_3)
                                              whereF
                                              nullRange
                   else if null diffVarSet_3
                        then C.Junction Con [tarPatF,whereF] nullRange
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_3)
                                              (C.Junction Con [tarPatF,whereF] nullRange)
                                              nullRange

    fst_sen = if souPatF == trueForm
              then if null diffVarSet_2
                   then snd_sen
                   else C.Quantification Universal 
                                         (varDeclFromRelVar diffVarSet_2)
                                         snd_sen
                                         nullRange
              else if null diffVarSet_2
                   then C.Relation souPatF Implication snd_sen nullRange
                   else C.Quantification Universal 
                                         (varDeclFromRelVar diffVarSet_2)
                                         (C.Relation souPatF
                                                     Implication 
                                                     snd_sen
                                                     nullRange)
                                         nullRange

  in 
    if null diffVarSet_1
    then C.Relation whenF Implication fst_sen nullRange
    else C.Quantification Universal 
                          (varDeclFromRelVar diffVarSet_1)
                          (C.Relation whenF
                                      Implication 
                                      fst_sen
                                      nullRange)
                          nullRange


-- The translation of Pattern = ⟨E, A, Pr⟩ is the formula r2 (x, y) ∧ Pr such
-- that r2 (x, y) is the translation of predicate p = ⟨r1 : C, r2 : D⟩ for every rel(p, x, y) ∈ A with x : C, y : D.

buildPatternFormula :: Pattern -> CASLFORMULA
buildPatternFormula (Pattern _ parRel patPred) = 
  let 
    relInvF = map (buildPatRelFormula) parRel
    oclExpF = [trueForm] --ToDo
  in 
    if null oclExpF
    then if null relInvF 
         then trueForm 
         else C.Junction Con relInvF nullRange
    else if null relInvF 
         then C.Junction Con oclExpF nullRange
         else C.Junction Con (relInvF ++ oclExpF) nullRange


buildPatRelFormula :: (CSMOF.PropertyT,RelVar,RelVar) -> CASLFORMULA
buildPatRelFormula (p,souV,tarV) =
  let 
    rName = CSMOF.targetRole p
    predTyp = [stringToId $ QVTRAs.varType souV, stringToId $ QVTRAs.varType tarV]
    varsInv = createVarRule [souV,tarV]
  in 
    Predication (C.Qual_pred_name (stringToId $ rName) (Pred_type predTyp nullRange) nullRange) 
                varsInv 
                nullRange


-- The translation of when = ⟨whenc , whenr⟩ is the formula Rule(v) ∧ whenc such that
-- Rule(v) is the translation of (Rulew , v) ∈ whenr. The translation of where is defined in a similar way.

buildWhenWhereFormula :: Maybe WhenWhere -> [RelVar] -> CASLFORMULA
buildWhenWhereFormula Nothing _ = trueForm -- ERROR, this cannot happens
buildWhenWhereFormula (Just (WhenWhere relInv oclExp)) varS =
  let
    relInvF = map (buildRelInvocFormula varS) relInv
    oclExpF = [trueForm] --ToDo
  in 
    if null oclExpF
    then if null relInvF 
         then trueForm 
         else C.Junction Con relInvF nullRange
    else if null relInvF 
         then C.Junction Con oclExpF nullRange
         else C.Junction Con (relInvF ++ oclExpF) nullRange


buildRelInvocFormula :: [RelVar] -> RelInvok -> CASLFORMULA
buildRelInvocFormula varS rel = 
  let 
    vars = QVTRAn.getSomething $ map (findRelVarFromName varS) (QVTRAs.params rel)
    varsInv = createVarRule vars
    predTyp = map (stringToId . varType) vars
  in 
    Predication (C.Qual_pred_name (stringToId $ QVTRAs.name rel) (Pred_type predTyp nullRange) nullRange) 
                varsInv 
                nullRange


-- | Translation of morphisms
mapMor :: QVTR.Morphism -> Result CASLMor
mapMor m = return C.Morphism
  { msource = mapSign $ domOfDefaultMorphism m
  , mtarget = mapSign $ codOfDefaultMorphism m
  , sort_map = Map.empty
  , op_map = Map.empty
  , pred_map = Map.empty
  , extended_map = ()
  }


-- mapSym :: QVTR.Symbol -> C.Symbol




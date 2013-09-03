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
import qualified Common.Lib.Rel as Rel


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
                            SimpleProp pN -> let sor = getSourceType pN prop
                                                 sor2 = getTargetType pN prop
                                             in Predication 
                                                  (C.Qual_pred_name (stringToId pN) 
                                                     (Pred_type [(stringToId sor),(stringToId sor2)] nullRange) 
                                                     nullRange) 
                                                  ((Qual_var x (stringToId typN) nullRange) :
                                                     [Qual_var v (stringToId sor2) nullRange]) 
                                                  nullRange
                            OppositeProp oPType oPName -> let sor = getTargetType oPName prop
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
  let sourceProp = findPropertyInHierarchy (CSMOF.typeRel $ QVTR.sourceSign qvtrSign) 
                                           (CSMOF.properties $ QVTR.sourceSign qvtrSign) typN pN
      targetProp = findPropertyInHierarchy (CSMOF.typeRel $ QVTR.targetSign qvtrSign) 
                                           (CSMOF.properties $ QVTR.targetSign qvtrSign) typN pN
  in
    case sourceProp of
      Nothing -> case targetProp of
                   Nothing -> (stringToId "", Nothing)
                   Just p -> (stringToId $ getTargetType pN p, Just p)
      Just p -> (stringToId $ getTargetType pN p, Just p)


getTargetType :: String -> CSMOF.PropertyT -> String
getTargetType pN p = 
  if (CSMOF.targetRole p) == pN
  then CSMOF.name (CSMOF.targetType p)
  else CSMOF.name (CSMOF.sourceType p)

getSourceType :: String -> CSMOF.PropertyT -> String
getSourceType pN p = 
  if (CSMOF.sourceRole p) == pN
  then CSMOF.name (CSMOF.targetType p)
  else CSMOF.name (CSMOF.sourceType p)


findPropertyInHierarchy :: Rel.Rel CSMOF.TypeClass -> Set.Set CSMOF.PropertyT -> String -> String -> Maybe CSMOF.PropertyT
findPropertyInHierarchy typRel props kType pN =
  let classes = kType : Set.toList (superClasses (Rel.map (CSMOF.name) typRel) kType)
  in findPropertyByTypeAndRole (Set.toList props) classes pN


findPropertyByTypeAndRole :: [CSMOF.PropertyT] -> [String] -> String -> Maybe CSMOF.PropertyT
findPropertyByTypeAndRole [] _ _ = Nothing
findPropertyByTypeAndRole (p : rest) classes pN =
  if (elem (CSMOF.name (CSMOF.sourceType p)) classes && (CSMOF.targetRole p) == pN) || 
     (elem (CSMOF.name (CSMOF.targetType p)) classes && (CSMOF.sourceRole p) == pN)
  then Just p
  else findPropertyByTypeAndRole rest classes pN


superClasses :: Rel.Rel String -> String -> Set.Set String
superClasses relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


createRuleFormula :: QVTR.Sign -> CASLSign -> QVTRAs.Relation -> CASLFORMULA
createRuleFormula _ _ _ = trueForm -- qvtrSign sig rels = trueForm


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




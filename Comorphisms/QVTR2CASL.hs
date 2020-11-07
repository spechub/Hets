{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/QVTR2CASL.hs
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
import qualified Common.Lib.Rel as Rel

import qualified Data.HashMap.Strict as Map
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
  return (cs, map (mapNamed $ mapSen s cs) ns ++ sentences cs )


mapSign :: QVTR.Sign -> CASLSign
mapSign s =
  let
    sSign = CSMOF2CASL.mapSign (sourceSign s)
    tSign = CSMOF2CASL.mapSign (targetSign s)
    relsProp = getPropertiesFromRelations (nonTopRelations s) (topRelations s)
    keysProp = getPropertiesFromKeys (keyDefs s)
    sUnion = C.uniteCASLSign sSign tSign
    everyProp = C.addMapSet (C.predMap sUnion) (C.addMapSet relsProp keysProp)
    sentRels = C.sentences sSign ++ C.sentences tSign
  in
    addStringSignature (replacePredMap (replaceSentences sUnion sentRels) everyProp)


getPropertiesFromRelations :: Map.HashMap String RuleDef -> Map.HashMap String RuleDef -> PredMap
getPropertiesFromRelations nonTopRel topRel = getRelDef $ Map.toList nonTopRel
                                               ++ Map.toList topRel -- TODO: might need sorting!


getRelDef :: [(String, RuleDef)] -> PredMap
getRelDef [] = MapSet.empty
getRelDef ((nam, rulDef) : rest) =
  let na = stringToId nam
      pa = foldr ((:) . stringToId . CSMOF.name) [] (QVTR.parameters rulDef)
  in MapSet.insert na (C.PredType pa) (getRelDef rest)


getPropertiesFromKeys :: [(String, String)] -> PredMap
getPropertiesFromKeys [] = MapSet.empty
getPropertiesFromKeys ((met, typ) : rest) =
  MapSet.insert (predKeyName met typ) (C.PredType []) (getPropertiesFromKeys rest)


predKeyName :: String -> String -> Id
predKeyName met typ = stringToId $ "key_" ++ met ++ "_" ++ typ


replacePredMap :: CASLSign -> PredMap -> CASLSign
replacePredMap (C.Sign sR rSR eSR oM aO _ vM s dS eD aM gA eI) predM =
  C.Sign sR rSR eSR oM aO predM vM s dS eD aM gA eI


replaceSentences :: CASLSign -> [Named CASLFORMULA] -> CASLSign
replaceSentences (C.Sign sR rSR eSR oM aO pM vM _ dS eD aM gA eI) sent =
  C.Sign sR rSR eSR oM aO pM vM sent dS eD aM gA eI


-- ------ Sentences

mapSen :: QVTR.Sign -> CASLSign -> QVTR.Sen -> CASLFORMULA
mapSen qvtrSign _ (KeyConstr k) = createKeyFormula qvtrSign k
mapSen qvtrSign sig (QVTSen r) = createRuleFormula qvtrSign sig r


createKeyFormula :: QVTR.Sign -> Key -> CASLFORMULA
createKeyFormula qvtrSign k =
  let
    souVars = CSMOF2CASL.generateVars "x" 2
    tarVars = CSMOF2CASL.generateVars "y" $ toInteger $ length $ properties k
    typeSouVar = stringToId (typeName k)
    souVarDec = Var_decl souVars typeSouVar nullRange
    (tarVarDec, props) = getVarFromKey qvtrSign tarVars (properties k) (typeName k)
    pname = predKeyName (metamodel k) (typeName k)
    equal = Negation (Equation (Qual_var (head souVars) typeSouVar nullRange)
                               Strong
                               (Qual_var (head $ tail souVars) typeSouVar nullRange)
                               nullRange)
                     nullRange
    sent = C.Relation equal
                      Implication
                      (C.Relation
                         (Junction Con (getPredicatesInvocation (mkSimpleId "x_1")
                           (typeName k) tarVars (properties k) props) nullRange)
                         Implication
                         (Junction Dis (map (`Negation` nullRange)
                                       (getPredicatesInvocation (mkSimpleId "x_2")
                          (typeName k) tarVars (properties k) props)) nullRange)
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
                                                     (Pred_type
                                                       [stringToId sor,
                                                        stringToId sor2]
                                                       nullRange) nullRange)
                                                  (Qual_var x (stringToId typN)
                                                    nullRange :
                                                   [Qual_var v (stringToId sor2)
                                                     nullRange]) nullRange
                            OppositeProp oPType oPName ->
                             let sor = QVTRAn.getTargetType oPName prop
                             in Predication
                                 (C.Qual_pred_name (stringToId oPName)
                                 (Pred_type [stringToId oPType,
                                             stringToId sor] nullRange)
                                   nullRange)
                                 (Qual_var v (stringToId oPType) nullRange :
                                  [Qual_var x (stringToId typN) nullRange])
                                nullRange
  in pr : getPredicatesInvocation x typN restV restP restPT
getPredicatesInvocation _ _ _ _ _ = []


getVarFromKey :: QVTR.Sign -> [VAR] -> [PropKey] -> String -> ([VAR_DECL], [Maybe CSMOF.PropertyT])
getVarFromKey _ [] [] _ = ([], [])
getVarFromKey qvtrSign (v : restV) (p : restP) typN =
  let
    (decl, prop) = case p of
                    SimpleProp pN -> let (idP, propT) = getSortOfProperty qvtrSign typN pN
                                     in (Var_decl [v] idP nullRange, propT)
                    OppositeProp oPType oPName -> let (_, propT) = getSortOfProperty qvtrSign oPType oPName
                                                  in (Var_decl [v] (stringToId oPType) nullRange, propT)
    (restD, restPr) = getVarFromKey qvtrSign restV restP typN
  in
    (decl : restD, prop : restPr)
getVarFromKey _ _ _ _ = ([], [])


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
createRuleFormula qvtSign _ (QVTR.RelationSen rDef varS parS souPat tarPat whenC whereC) =
  let
    rName = QVTR.name rDef
    parTyp = map (stringToId . varType) parS

    whenVarSet = collectWhenVarSet varS whenC

    souVarInOCL = foldr (\ (_, _, ocl) l -> l ++ getVarIdsFromOCLExpre varS ocl)
                   [] (QVTR.patPreds souPat)
    souDomVarSet = Set.fromList (QVTR.patVarSet souPat ++ souVarInOCL)

    tarVarInOCL = foldr (\ (_, _, ocl) l -> l ++ getVarIdsFromOCLExpre varS ocl)
                   [] (QVTR.patPreds tarPat)
    tarDomVarSet = Set.fromList (QVTR.patVarSet tarPat ++ tarVarInOCL)

    whereVarSet = Set.fromList $ collectWhenVarSet varS whereC

    varSet_2 = Set.difference (Set.difference (Set.union tarDomVarSet whereVarSet) (Set.fromList whenVarSet)) souDomVarSet

  in
    if null parS
    then C.Relation
           (C.Predication (C.Qual_pred_name (stringToId rName) (Pred_type parTyp nullRange) nullRange)
                          []
                          nullRange)
           C.Equivalence
           (if null whenVarSet
            then buildEmptyWhenFormula qvtSign parS varS varSet_2 souPat tarPat whereC
            else buildNonEmptyWhenFormula qvtSign whenVarSet parS varS varSet_2 souPat tarPat whenC whereC)
           nullRange
    else Quantification Universal (varDeclFromRelVar parS)
                        (C.Relation (C.Predication (C.Qual_pred_name (stringToId rName) (Pred_type parTyp nullRange) nullRange)
                                                   (createVarRule parS)
                                                   nullRange)
                                    C.Equivalence
                                    (if null whenVarSet
                                     then buildEmptyWhenFormula qvtSign parS varS varSet_2 souPat tarPat whereC
                                     else buildNonEmptyWhenFormula qvtSign whenVarSet parS varS varSet_2 souPat tarPat whenC whereC)
                                    nullRange)
                        nullRange


createVarRule :: [RelVar] -> [C.CASLTERM]
createVarRule = map (\ v -> Qual_var (mkSimpleId $ varName v)
                                    (stringToId $ varType v) nullRange)

collectWhenVarSet :: [RelVar] -> Maybe QVTRAs.WhenWhere -> [RelVar]
collectWhenVarSet _ Nothing = []
collectWhenVarSet varS (Just (WhenWhere relInv oclExp)) =
  let
    relVars = QVTRAn.getSomething $ map (findRelVarFromName varS)
               (concatMap QVTRAs.params relInv)
    oclExpVars = foldr ((++) . getVarIdsFromOCLExpre varS) [] oclExp
  in
    relVars ++ oclExpVars


findRelVarFromName :: [RelVar] -> String -> Maybe RelVar
findRelVarFromName [] _ = Nothing
findRelVarFromName (v : restV) nam = if QVTRAs.varName v == nam
                                     then Just v
                                     else findRelVarFromName restV nam


getVarIdsFromOCLExpre :: [RelVar] -> QVTRAs.OCL -> [RelVar]
getVarIdsFromOCLExpre varS (StringExp str) = getVarIdsFromStrExpre varS str
getVarIdsFromOCLExpre varS (Paren expr) = getVarIdsFromOCLExpre varS expr
getVarIdsFromOCLExpre varS (NotB expr) = getVarIdsFromOCLExpre varS expr
getVarIdsFromOCLExpre varS (AndB exp1 exp2) = getVarIdsFromOCLExpre varS exp1
 ++ getVarIdsFromOCLExpre varS exp2
getVarIdsFromOCLExpre varS (OrB exp1 exp2) = getVarIdsFromOCLExpre varS exp1
 ++ getVarIdsFromOCLExpre varS exp2
getVarIdsFromOCLExpre varS (Equal str1 str2) = getVarIdsFromStrExpre varS str1
 ++ getVarIdsFromStrExpre varS str2
getVarIdsFromOCLExpre _ _ = []


getVarIdsFromStrExpre :: [RelVar] -> QVTRAs.STRING -> [RelVar]
getVarIdsFromStrExpre varS (ConcatExp str1 str2) =
 getVarIdsFromStrExpre varS str1 ++ getVarIdsFromStrExpre varS str2
getVarIdsFromStrExpre varS (VarExp v) = case findRelVarFromName varS v of
                                          Nothing -> []
                                          Just r -> [r]
getVarIdsFromStrExpre _ _ = []


{- 1. WhenVarSet = ∅
∀ x1 , ..., xn ∈ (VarSet\2_VarSet)\ParSet,
(Pattern1 → ∃ y1 , ..., ym ∈ 2_VarSet\ParSet, (Pattern2 ∧ where)) -}

buildEmptyWhenFormula :: QVTR.Sign -> [RelVar] -> [RelVar] -> Set.Set RelVar -> Pattern -> Pattern -> Maybe WhenWhere -> CASLFORMULA
buildEmptyWhenFormula qvtSign parS varS varSet_2 souPat tarPat whereC =
  let
    listPars = Set.fromList parS
    diffVarSet_1 = Set.toList $ Set.difference (Set.difference (Set.fromList varS) varSet_2) listPars
    diffVarSet_2 = Set.toList $ Set.difference varSet_2 listPars
    souPatF = buildPatternFormula qvtSign varS souPat
    tarPatF = buildPatternFormula qvtSign varS tarPat
    whereF = buildWhenWhereFormula whereC varS

    fst_sen | whereF == trueForm =
                   if tarPatF == trueForm
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
            | tarPatF == trueForm =
                        if null diffVarSet_2
                        then whereF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_2)
                                              whereF
                                              nullRange
            | null diffVarSet_2 = C.Junction Con [tarPatF, whereF] nullRange
            | otherwise = C.Quantification Existential
                                    (varDeclFromRelVar diffVarSet_2)
                                    (C.Junction Con [tarPatF, whereF] nullRange)
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
varDeclFromRelVar = map (\ v -> Var_decl [mkSimpleId $ varName v]
                                 (stringToId $ varType v) nullRange)

{- 2. WhenVarSet <> ∅
∀ z1 , ..., zo ∈ WhenVarSet\ParSet, (when →
∀ x1 , ..., xn ∈ (VarSet\(WhenVarSet ∪ 2_VarSet))\ParSet, (Pattern1 →
∃ y1 , ..., ym ∈ 2_VarSet\ParSet, (Pattern2 ∧ where))) -}

buildNonEmptyWhenFormula :: QVTR.Sign -> [RelVar] -> [RelVar] -> [RelVar] -> Set.Set RelVar
                                      -> Pattern -> Pattern -> Maybe WhenWhere -> Maybe WhenWhere -> CASLFORMULA
buildNonEmptyWhenFormula qvtSign whenVarSet parS varS varSet_2 souPat tarPat whenC whereC =
  let
    listWhenVars = Set.fromList whenVarSet
    listPars = Set.fromList parS
    diffVarSet_1 = Set.toList $ Set.difference listWhenVars listPars
    diffVarSet_2 = Set.toList $ Set.difference (Set.difference (Set.fromList varS) (Set.union listWhenVars varSet_2)) listPars
    diffVarSet_3 = Set.toList $ Set.difference varSet_2 listPars
    souPatF = buildPatternFormula qvtSign varS souPat
    tarPatF = buildPatternFormula qvtSign varS tarPat
    whenF = buildWhenWhereFormula whenC varS
    whereF = buildWhenWhereFormula whereC varS

    snd_sen | whereF == trueForm =
                   if tarPatF == trueForm
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
            | tarPatF == trueForm =
                        if null diffVarSet_3
                        then whereF
                        else C.Quantification Existential
                                              (varDeclFromRelVar diffVarSet_3)
                                              whereF
                                              nullRange
            | null diffVarSet_3 = C.Junction Con [tarPatF, whereF] nullRange
            | otherwise = C.Quantification Existential
                                    (varDeclFromRelVar diffVarSet_3)
                                    (C.Junction Con [tarPatF, whereF] nullRange)
                                    nullRange

    fst_sen | souPatF == trueForm =
                   if null diffVarSet_2
                   then snd_sen
                   else C.Quantification Universal
                                         (varDeclFromRelVar diffVarSet_2)
                                         snd_sen
                                         nullRange
            | null diffVarSet_2 = C.Relation souPatF Implication snd_sen nullRange
            | otherwise = C.Quantification Universal
                                    (varDeclFromRelVar diffVarSet_2)
                                    (C.Relation souPatF
                                                Implication
                                                snd_sen
                                                nullRange) nullRange
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


{- The translation of Pattern = ⟨E, A, Pr⟩ is the formula r2 (x, y) ∧ Pr such
that r2 (x, y) is the translation of predicate p = ⟨r1 : C, r2 : D⟩ for every rel(p, x, y) ∈ A with x : C, y : D. -}

buildPatternFormula :: QVTR.Sign -> [RelVar] -> Pattern -> CASLFORMULA
buildPatternFormula qvtSign varS (Pattern _ parRel patPred) =
  let
    relInvF = map buildPatRelFormula parRel
    oclExpF = map (buildOCLFormulaWRel qvtSign varS) patPred
  in
    if null oclExpF
    then if null relInvF
         then trueForm
         else C.Junction Con relInvF nullRange
    else if null relInvF
         then C.Junction Con oclExpF nullRange
         else C.Junction Con (relInvF ++ oclExpF) nullRange


buildPatRelFormula :: (CSMOF.PropertyT, RelVar, RelVar) -> CASLFORMULA
buildPatRelFormula (p, souV, tarV) =
  let
    rName = CSMOF.targetRole p
    predTyp = [stringToId $ CSMOF.name $ CSMOF.sourceType p, stringToId $
               CSMOF.name $ CSMOF.targetType p]
    varsInv = createVarRule [souV, tarV]
  in
    Predication (C.Qual_pred_name (stringToId rName) (Pred_type predTyp nullRange) nullRange)
                varsInv
                nullRange


{- The translation of when = ⟨whenc , whenr⟩ is the formula Rule(v) ∧ whenc such that
Rule(v) is the translation of (Rulew , v) ∈ whenr. The translation of where is defined in a similar way. -}

buildWhenWhereFormula :: Maybe WhenWhere -> [RelVar] -> CASLFORMULA
buildWhenWhereFormula Nothing _ = trueForm -- ERROR, this cannot happens
buildWhenWhereFormula (Just (WhenWhere relInv oclExp)) varS =
  let
    relInvF = map (buildRelInvocFormula varS) relInv
    oclExpF = map (buildOCLFormula varS) oclExp
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
    C.Predication (C.Qual_pred_name (stringToId $ QVTRAs.name rel)
      (Pred_type predTyp nullRange) nullRange) varsInv nullRange


buildOCLFormulaWRel :: QVTR.Sign -> [RelVar] -> (String, String, OCL) -> CASLFORMULA
buildOCLFormulaWRel qvtSign varS (prN, varN, StringExp str) =
  let oclT = buildSTRINGTerm str varS
      typ = case findRelVarFromName varS varN of
              Nothing -> ""
              Just v -> varType v

      (_, p) = getSortOfProperty qvtSign typ prN
      (sor, sor2) = case p of
                     Nothing -> (stringToId "", stringToId "")
                     Just pp -> if CSMOF.targetRole pp == prN
                      then (stringToId $ CSMOF.name $ CSMOF.sourceType pp,
                            stringToId $ CSMOF.name $ CSMOF.targetType pp)
                      else (stringToId $ CSMOF.name $ CSMOF.targetType pp,
                            stringToId $ CSMOF.name $ CSMOF.sourceType pp)
  in
    C.Predication (C.Qual_pred_name (stringToId prN) (Pred_type [sor, sor2]
      nullRange) nullRange)
     (Qual_var (mkSimpleId varN) (stringToId typ) nullRange : [oclT]) nullRange
buildOCLFormulaWRel _ _ _ = trueForm


buildOCLFormula :: [RelVar] -> OCL -> CASLFORMULA
buildOCLFormula varS (Paren e) = buildOCLFormula varS e
buildOCLFormula _ (BExp b) = if b then trueForm else C.Negation trueForm nullRange
buildOCLFormula varS (NotB e) = C.Negation (buildOCLFormula varS e) nullRange
buildOCLFormula varS (AndB lE rE) = C.Junction Con [buildOCLFormula varS lE,
                                     buildOCLFormula varS rE] nullRange
buildOCLFormula varS (OrB lE rE) = C.Junction Dis [buildOCLFormula varS lE,
                                     buildOCLFormula varS rE] nullRange
buildOCLFormula varS (Equal lE rE) = C.Equation (buildSTRINGTerm lE varS)
                                      Strong (buildSTRINGTerm rE varS) nullRange
buildOCLFormula _ (StringExp _) = trueForm -- This is not a formula, but a term used within an equality


buildSTRINGTerm :: STRING -> [RelVar] -> CASLTERM
buildSTRINGTerm (Str str) _ = C.Application (Qual_op_name (stringToId str)
  (Op_type Total [] (stringToId "String") nullRange) nullRange) [] nullRange
buildSTRINGTerm (ConcatExp lS rS) varS =
  let
    lSTerm = buildSTRINGTerm lS varS
    rSTerm = buildSTRINGTerm rS varS
    stringSort = stringToId "String"
  in
    C.Application (Qual_op_name (stringToId "++")
                                (Op_type Total [stringSort, stringSort] stringSort nullRange)
                                nullRange)
                  [lSTerm, rSTerm]
                  nullRange
buildSTRINGTerm (VarExp vE) varS =
  let
    var = case findRelVarFromName varS vE of
            Nothing -> stringToId ""
            Just v -> stringToId $ varType v
  in
    Qual_var (mkSimpleId vE) var nullRange


{- getSTRINGType :: STRING -> [RelVar] -> SORT
getSTRINGType (VarExp vE) varS =
case findRelVarFromName varS vE of
Nothing -> stringToId ""
Just v -> stringToId $ varType v
getSTRINGType _ _ = stringToId "" -}


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


{- 1) Adds the String primitive type within a CASL Signature
2) Generates the strings concatenation operation ++ -}

addStringSignature :: CASLSign -> CASLSign
addStringSignature s =
  let
    stringSort = stringToId "String"
    (strObj, othObj) = separateStringConstraintFromOthers $ sentences s
{- strObjTr = getStringObjFromTransformation ns
strObjOps = foldr (\(idd,opT) se -> MapSet.insert idd opT se) MapSet.empty (getStringOperations strObjTr) -}
    everyString = Set.toList (getStringObjects strObj) -- Set.toList (Set.union strObjTr (getStringObjects strObj))
    concatOp = mkTotOpType [stringSort, stringSort] stringSort
  in
    C.Sign { sortRel = Rel.insertPair stringSort stringSort (C.sortRel s)
           , revSortRel = C.revSortRel s
           , emptySortSet = C.emptySortSet s
           , opMap = MapSet.insert (stringToId "++") concatOp (C.opMap s) -- MapSet.union strObjOps (C.opMap s)
           , assocOps = C.assocOps s
           , predMap = C.predMap s
           , varMap = C.varMap s
           , sentences = getNoConfusionStrings everyString :
                           (toStringConstraint (stringSort, everyString) :
                             deleteNoConfusionString othObj)
           , declaredSymbols = C.declaredSymbols s
           , envDiags = C.envDiags s
           , annoMap = C.annoMap s
           , globAnnos = C.globAnnos s
           , extendedInfo = C.extendedInfo s
           }


{- splitStringByUnderscore :: String -> [String]
splitStringByUnderscore [] = []
splitStringByUnderscore str =
let
strAux = getUntilUnderscore str
rest = splitStringByUnderscore (drop (length strAux + 1) str)
in
strAux : rest -}


{- getUntilUnderscore :: String -> String
getUntilUnderscore [] = []
getUntilUnderscore (s : restS) = if s == '_'
then []
else s : getUntilUnderscore restS -}


{- getStringOperations :: Set.Set Id -> [(Id,OpType)]
getStringOperations ids = Set.fold (\idd lis -> (idd, (mkTotOpType [] (stringToId "String"))) : lis ) [] ids -}


deleteNoConfusionString :: [Named CASLFORMULA] -> [Named CASLFORMULA]
deleteNoConfusionString [] = []
deleteNoConfusionString (nf : restNF) =
  let rest = deleteNoConfusionString restNF
  in if startswith (senAttr nf) "noConfusion_String"
     then rest
     else nf : rest


startswith :: String -> String -> Bool
startswith [] [] = True
startswith (a : restA) (b : restB) = a == b && startswith restA restB
startswith _ _ = False


getNoConfusionStrings :: [Id] -> Named CASLFORMULA
getNoConfusionStrings ordObj =
  let diffForm = foldr ((++) . diffOfRestStringOps ordObj) [] ordObj
  in makeNamed "noConfusion_String" (Junction Con diffForm nullRange)


diffOfRestStringOps :: [Id] -> Id -> [CASLFORMULA]
diffOfRestStringOps lisObj objName =
  let lis = removeUntilId lisObj objName
  in concatMap (diffOpsStr objName) lis


removeUntilId :: [Id] -> Id -> [Id]
removeUntilId lis str =
  case lis of
    [] -> []
    a : rest -> if a == str
                then rest
                else removeUntilId rest str


diffOpsStr :: Id -> Id -> [CASLFORMULA]
diffOpsStr objName1 objName2 =
  [Negation (Equation
                 (Application (Qual_op_name objName1
                        (Op_type Total [] (stringToId "String") nullRange)
                        nullRange) [] nullRange)
                 Strong
                 (Application (Qual_op_name objName2
                        (Op_type Total [] (stringToId "String") nullRange)
                        nullRange) [] nullRange)
                 nullRange)
       nullRange | objName1 /= objName2]

{- Get String instances within transformation rules
getStringObjFromTransformation :: [Named QVTR.Sen] -> Set.Set Id
getStringObjFromTransformation [] = Set.empty
getStringObjFromTransformation (ns : restNS) =
let
restId = getStringObjFromTransformation restNS
idSen = case sentence ns of
QVTSen rel -> getStringIdsFromRelation rel
_ -> Set.empty
in
Set.union idSen restId -}


{- getStringIdsFromRelation :: RelationSen -> Set.Set Id
getStringIdsFromRelation (RelationSen _ _ _ souP tarP whenCl whereCl) =
let
souPId = getStringIdsFromPattern souP
tarPId = getStringIdsFromPattern tarP
whenId = getStringIdsFromWhenWhere whenCl
whereId = getStringIdsFromWhenWhere whereCl
in
Set.unions [souPId,tarPId,whenId,whereId] -}


{- getStringIdsFromPattern :: Pattern -> Set.Set Id
getStringIdsFromPattern (Pattern _ _ p) = getStringIdsFromOclPred p -}


{- getStringIdsFromOclPred :: [(String,String,OCL)] -> Set.Set Id
getStringIdsFromOclPred [] = Set.empty
getStringIdsFromOclPred ((_,_,ocl) : restPr) = Set.union (getStringIdsFromOCL ocl) (getStringIdsFromOclPred restPr) -}


{- getStringIdsFromWhenWhere :: Maybe WhenWhere -> Set.Set Id
getStringIdsFromWhenWhere Nothing = Set.empty
getStringIdsFromWhenWhere (Just (WhenWhere _ ocl)) = Set.unions (map (getStringIdsFromOCL) ocl) -}


{- getStringIdsFromOCL :: OCL -> Set.Set Id
getStringIdsFromOCL (Paren e) = getStringIdsFromOCL e
getStringIdsFromOCL (StringExp str) = getStringIdsFromString str
getStringIdsFromOCL (BExp _) = Set.empty
getStringIdsFromOCL (NotB no) = getStringIdsFromOCL no
getStringIdsFromOCL (AndB lE rE) = Set.union (getStringIdsFromOCL lE) (getStringIdsFromOCL rE)
getStringIdsFromOCL (OrB lE rE) = Set.union (getStringIdsFromOCL lE) (getStringIdsFromOCL rE)
getStringIdsFromOCL (Equal lE rE) = Set.union (getStringIdsFromString lE) (getStringIdsFromString rE) -}


{- getStringIdsFromString :: STRING -> Set.Set Id
getStringIdsFromString (Str s) = if s == ""
then Set.insert (stringToId "EMPTY") Set.empty
else Set.insert (stringToId s) Set.empty
getStringIdsFromString (ConcatExp lS rS) = Set.union (getStringIdsFromString lS) (getStringIdsFromString rS)
getStringIdsFromString (VarExp _) = Set.empty -}


-- Separate string free type contraints (derived from each metamodel) from the others
separateStringConstraintFromOthers :: [Named CASLFORMULA] -> ([Named CASLFORMULA],
                                      [Named CASLFORMULA])
separateStringConstraintFromOthers [] = ([], [])
separateStringConstraintFromOthers (f : restF) =
  let (restString, restOther) = separateStringConstraintFromOthers restF
  in case sentence f of
       Sort_gen_ax [Constraint sor _ _] _ -> if sor == stringToId "String"
                                             then (f : restString, restOther)
                                             else (restString, f : restOther)
       _ -> (restString, f : restOther)


-- Get String names from Qual_op_name
getStringObjects :: [Named CASLFORMULA] -> Set.Set Id
getStringObjects [] = Set.empty
getStringObjects (f : restF) =
  case sentence f of
    Sort_gen_ax [Constraint _ listObj _] _ -> Set.union
     (getObjNamesFromOp listObj) (getStringObjects restF)
    _ -> getStringObjects restF


getObjNamesFromOp :: [(OP_SYMB, [Int])] -> Set.Set Id
getObjNamesFromOp [] = Set.empty
getObjNamesFromOp ((op, _) : restOp) =
  case op of
    Qual_op_name obj _ _ -> Set.insert obj (getObjNamesFromOp restOp)
    _ -> getObjNamesFromOp restOp


{- Generate free type
String ::= EMPTY | ... (string instances) ...
__ ++ __ (first: String; rest: String) -}

toStringConstraint :: (Id, [Id]) -> Named CASLFORMULA
toStringConstraint (sor, lisObj) =
  let
    stringSort = stringToId "String"
    concatOp = (Qual_op_name (stringToId "++") (Op_type Total
      [stringSort, stringSort] stringSort nullRange) nullRange, [])
    simplCon = Constraint sor (concatOp : foldr ((:) . toConstraintFromId sor)
      [] lisObj) sor
    constr = mkSort_gen_ax [simplCon] True
  in
    makeNamed "sortGenCon_String" constr

toConstraintFromId :: Id -> Id -> (OP_SYMB, [Int])
toConstraintFromId sor obj = (Qual_op_name obj (Op_type Total [] sor nullRange)
  nullRange, [])

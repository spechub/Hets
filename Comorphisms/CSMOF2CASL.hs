{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Coding CSMOF into CASL
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module Comorphisms.CSMOF2CASL
    ( CSMOF2CASL (..), mapSign, generateVars
    ) where

import Logic.Logic
import Logic.Comorphism
import Common.DefaultMorphism

-- CSMOF
import CSMOF.Logic_CSMOF as CSMOF
import CSMOF.As as CSMOFAs
import CSMOF.Sign as CSMOF

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL as C
import CASL.Sublogic
import CASL.Sign as C
import CASL.Morphism as C

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.ProofTree
import Common.Result

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

-- | lid of the morphism
data CSMOF2CASL = CSMOF2CASL deriving Show

instance Language CSMOF2CASL -- default is ok

instance Comorphism CSMOF2CASL
    CSMOF.CSMOF
    ()
    CSMOFAs.Metamodel
    CSMOF.Sen
    ()
    ()
    CSMOF.Sign
    CSMOF.Morphism
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
      sourceLogic CSMOF2CASL = CSMOF
      sourceSublogic CSMOF2CASL = ()
      targetLogic CSMOF2CASL = CASL
      mapSublogic CSMOF2CASL _ = Just $ caslTop
        { has_part = False
        , sub_features = LocFilSub
        , cons_features = SortGen True True }
      map_theory CSMOF2CASL = mapTheory
      map_sentence CSMOF2CASL s = return . mapSen (mapSign s)
      map_morphism CSMOF2CASL = mapMor
      -- map_symbol CSMOF2CASL _ = Set.singleton . mapSym
      is_model_transportable CSMOF2CASL = True
      has_model_expansion CSMOF2CASL = True
      is_weakly_amalgamable CSMOF2CASL = True
      isInclusionComorphism CSMOF2CASL = True


mapTheory :: (CSMOF.Sign, [Named CSMOF.Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = let cs = mapSign s in
  return (cs, map (mapNamed $ mapSen cs) ns ++ sentences cs)


mapSign :: CSMOF.Sign -> CASLSign
mapSign s =
  let
    sorts = getSorts (types s) (typeRel s)
    ops = getOperations (instances s)
    predd = getPredicates (properties s)
    sent = getSentencesRels (links s) (instances s)
    sentDisEmb = getSortGen (typeRel s) (abstractClasses s) (types s) (instances s)
    noConfBetOps = getNoConfusionBetweenSets (instances s) (typeRel s)
  in
    C.Sign
    { sortRel = sorts
    , revSortRel = Just $ Rel.fromList (map revertOrder (Rel.toList sorts))
    , emptySortSet = Set.empty
    , opMap = ops
    , assocOps = MapSet.empty
    , predMap = fst predd
    , varMap = Map.empty
    , sentences = snd predd ++ sent ++ sentDisEmb ++ noConfBetOps
    , declaredSymbols = Set.empty
    , envDiags = []
    , annoMap = MapSet.empty
    , globAnnos = emptyGlobalAnnos
    , extendedInfo = ()
    }

getSorts :: Set.Set TypeClass -> Rel.Rel TypeClass -> Rel.Rel SORT
getSorts setC relC =
  let relS = Set.fold (insertSort . name) Rel.empty setC
  in foldr insertPair relS (Rel.toList relC)

insertSort :: String -> Rel.Rel SORT -> Rel.Rel SORT
insertSort s = Rel.insertPair (stringToId s) (stringToId s)

insertPair :: (TypeClass, TypeClass) -> Rel.Rel SORT -> Rel.Rel SORT
insertPair (t1, t2) = Rel.insertPair (stringToId $ name t1) (stringToId $ name t2)

revertOrder :: (SORT, SORT) -> (SORT, SORT)
revertOrder (a, b) = (b, a)

getPredicates :: Set.Set PropertyT -> (PredMap, [Named (FORMULA f)])
getPredicates = Set.fold insertPredicate (MapSet.empty, [])

insertPredicate :: PropertyT -> (PredMap, [Named (FORMULA f)]) -> (PredMap, [Named (FORMULA f)])
insertPredicate prop (predM, form) =
  let
    sort1 = stringToId $ name $ sourceType prop
    sort2 = stringToId $ name $ targetType prop
    pname1 = stringToId $ targetRole prop
    ptype1 = PredType $ sort1 : [sort2]
    pname2 = stringToId $ sourceRole prop
    ptype2 = PredType $ sort2 : [sort1]
    nam = "equiv_" ++ targetRole prop ++ "_" ++ sourceRole prop
    varsD = [Var_decl [mkSimpleId "x"] sort2 nullRange,
             Var_decl [mkSimpleId "y"] sort1 nullRange]
    sentRel = C.Relation
                (C.Predication (C.Qual_pred_name pname2
                   (Pred_type [sort2, sort1] nullRange) nullRange)
                    (C.Qual_var (mkSimpleId "x") sort2 nullRange :
                       [C.Qual_var (mkSimpleId "y") sort1 nullRange]) nullRange)
                C.Equivalence
                 (C.Predication (C.Qual_pred_name pname1
                   (Pred_type [sort1, sort2] nullRange) nullRange)
                   (C.Qual_var (mkSimpleId "y") sort1 nullRange :
                     [C.Qual_var (mkSimpleId "x") sort2 nullRange]) nullRange)
              nullRange
    sent = Quantification Universal varsD sentRel nullRange
  in
    {- MapSet does not allows repeated elements, but predicate names can be repeated
    (this must be corrected by creating a more complex ID) -}
    if sourceRole prop == "_"
    then (MapSet.insert pname1 ptype1 predM, form)
    else if targetRole prop == "_"
         then (MapSet.insert pname2 ptype2 predM, form)
         else (MapSet.insert pname1 ptype1 $ MapSet.insert pname2 ptype2 predM,
               makeNamed nam sent : form)


getOperations :: Map.Map String TypeClass -> OpMap
getOperations ops = foldr insertOperations MapSet.empty (Map.toList ops)

insertOperations :: (String, TypeClass) -> OpMap -> OpMap
insertOperations (na, tc) opM =
  let
    opName = stringToId na
    opType = OpType Total [] (stringToId $ name tc)
  in
    MapSet.insert opName opType opM


getSentencesRels :: Set.Set LinkT -> Map.Map String TypeClass ->
                    [Named CASLFORMULA]
getSentencesRels = completenessOfRelations


completenessOfRelations :: Set.Set LinkT -> Map.Map String TypeClass ->
                           [Named CASLFORMULA]
completenessOfRelations linkk ops =
  let ordLinks = getLinksByProperty linkk
  in foldr ((++) . createComplFormula ops) [] (Map.toList ordLinks)

createComplFormula :: Map.Map String TypeClass -> (String, [LinkT]) ->
                      [Named CASLFORMULA]
createComplFormula ops (nam, linksL) =
  let
    varA = mkSimpleId "x"
    varB = mkSimpleId "y"
  in
    case linksL of
      [] -> []
      LinkT _ _ pr : _ ->
       let sorA = stringToId $ name $ sourceType pr
           sorB = stringToId $ name $ targetType pr
           varsD = [Var_decl [varA] sorA nullRange,
                    Var_decl [varB] sorB nullRange]
           sent = C.Relation (C.Predication (C.Qual_pred_name
            (stringToId $ targetRole pr) (Pred_type [sorA, sorB] nullRange)
            nullRange) (C.Qual_var varA sorA nullRange :
             [C.Qual_var varB sorB nullRange]) nullRange)
            C.Equivalence (Junction Dis
              (foldr ((:) . getPropHold ops varA sorA varB sorB) [] linksL)
               nullRange) nullRange
           sentQuan = Quantification Universal varsD sent nullRange
       in [makeNamed ("compRel_" ++ nam) sentQuan]

getPropHold :: Map.Map String TypeClass -> VAR -> SORT -> VAR -> SORT -> LinkT
               -> CASLFORMULA
getPropHold ops varA sorA varB sorB lin =
  let
    souObj = Map.lookup (sourceVar lin) ops
    tarObj = Map.lookup (targetVar lin) ops
    typSou = case souObj of
               Nothing -> sourceVar lin -- if happens then is an error
               Just tSou -> name tSou
    typTar = case tarObj of
               Nothing -> targetVar lin -- if happens then is an error
               Just tTar -> name tTar
    eqA = Equation (Qual_var varA sorA nullRange)
                   Strong
                     (Application (Qual_op_name (stringToId (sourceVar lin))
                        (Op_type Total [] (stringToId typSou) nullRange)
                        nullRange) [] nullRange)
                   nullRange
    eqB = Equation (Qual_var varB sorB nullRange)
                   Strong
                   (Application (Qual_op_name (stringToId (targetVar lin))
                        (Op_type Total [] (stringToId typTar) nullRange)
                        nullRange) [] nullRange)
                   nullRange
  in
    Junction Con (eqA : [eqB]) nullRange


getLinksByProperty :: Set.Set LinkT -> Map.Map String [LinkT]
getLinksByProperty linkk =
  let elems = Set.elems linkk
  in foldr getByProperty Map.empty elems

getByProperty :: LinkT -> Map.Map String [LinkT] -> Map.Map String [LinkT]
getByProperty lin mapL =
  let
    prope = CSMOF.property lin
    nameLook = sourceRole prope ++ name (sourceType prope) ++ targetRole prope
                ++ name (targetType prope)
    setProp = Map.lookup nameLook mapL
  in
    case setProp of
      Nothing -> Map.insert nameLook [lin] (Map.delete nameLook mapL)
      Just s -> Map.insert nameLook (lin : s) (Map.delete nameLook mapL)


getSortGen :: Rel.Rel TypeClass -> Set.Set TypeClass -> Set.Set TypeClass ->
              Map.Map String TypeClass -> [Named CASLFORMULA]
getSortGen typpR absCl typCl inst = disjointEmbedding absCl typpR ++
 sortGeneration inst ++
 sortGenerationNonAbstractSuperClasses typpR typCl absCl inst


-- Free type of non-abstract superclasses
sortGenerationNonAbstractSuperClasses :: Rel.Rel TypeClass -> Set.Set TypeClass
 -> Set.Set TypeClass -> Map.Map String TypeClass -> [Named CASLFORMULA]
sortGenerationNonAbstractSuperClasses typpR typCl absCl inst =
  let
    ordObj = foldr orderByClass Map.empty (Map.toList inst)
    nonAbsClasses = getNonAbstractClasess absCl typCl
    nonAbsClassesWChilds = filter (not . null . snd)
     (Set.fold ((:) . getSubClasses typpR) [] nonAbsClasses)
    childObjects = foldr ((:) . getClassSubObjects ordObj)
     [] nonAbsClassesWChilds -- [(TypeClass,[String])]
  in
    foldr ((:) . toSortConstraintNonAbsClass inst) [] childObjects


-- Takes the objects, and a class with its child classes and returns the descendent objects of such class
getClassSubObjects :: Map.Map TypeClass [String] -> (TypeClass, [TypeClass]) ->
                      (TypeClass, [String])
getClassSubObjects objs (tc, subCl) =
  let objTC = findObjectInMap objs tc
  in
    (tc, objTC ++ foldr ((++) . findObjectInMap objs) [] subCl)

findObjectInMap :: Map.Map TypeClass [String] -> TypeClass -> [String]
findObjectInMap objs tc = fromMaybe [] $ Map.lookup tc objs

getNonAbstractClasess :: Set.Set TypeClass -> Set.Set TypeClass -> Set.Set TypeClass
getNonAbstractClasess absCl classes = Set.difference classes absCl

getSubClasses :: Rel.Rel TypeClass -> TypeClass -> (TypeClass, [TypeClass])
getSubClasses typpR tc =
  let subCla = map fst (filter (isParent tc) (Rel.toList typpR))
      rec = foldr ((++) . snd . getSubClasses typpR) [] subCla
  in (tc, subCla ++ rec)

isParent :: TypeClass -> (TypeClass, TypeClass) -> Bool
isParent tc (_, tc2) = tc == tc2

toSortConstraintNonAbsClass :: Map.Map String TypeClass -> (TypeClass, [String])
                               -> Named CASLFORMULA
toSortConstraintNonAbsClass inst (tc, lisObj) =
  let
    sor = stringToId $ name tc
    varA = Var_decl [mkSimpleId "x"] sor nullRange
    sent = Junction Dis (foldr ((:) . getEqualityVarObject sor inst)
      [] lisObj) nullRange
    constr = Quantification Universal [varA] sent nullRange
  in
    makeNamed ("sortGenCon_" ++ name tc) constr

getEqualityVarObject :: SORT -> Map.Map String TypeClass -> String -> CASLFORMULA
getEqualityVarObject sor inst obj =
  let oTyp = case Map.lookup obj inst of
                Nothing -> stringToId obj -- If happens, there is an error
                Just ob -> stringToId $ name ob
  in
    Equation (Qual_var (mkSimpleId "x") sor nullRange)
      Strong
      (Application (Qual_op_name (stringToId obj)
        (Op_type Total [] oTyp nullRange)
        nullRange) [] nullRange)
      nullRange


-- Sorts are generated as a free type of object functions
sortGeneration :: Map.Map String TypeClass -> [Named CASLFORMULA]
sortGeneration inst =
  let
    ordObj = foldr orderByClass Map.empty (Map.toList inst)
    noJunk = foldr ((:) . toSortConstraint) [] (Map.toList ordObj)
  in
    noJunk

mapFilterJust :: [Maybe a] -> [a]
mapFilterJust list =
  case list of
    [] -> []
    a : rest -> case a of
                  Nothing -> mapFilterJust rest
                  Just el -> el : mapFilterJust rest

orderByClass :: (String, TypeClass) -> Map.Map TypeClass [String] ->
                Map.Map TypeClass [String]
orderByClass (ob, tc) mapTC =
  case Map.lookup tc mapTC of
    Nothing -> Map.insert tc [ob] mapTC
    Just listObj -> Map.insert tc (ob : listObj) (Map.delete tc mapTC)


getNoConfusionBetweenSets :: Map.Map String TypeClass -> Rel.Rel TypeClass ->
                             [Named CASLFORMULA]
getNoConfusionBetweenSets inst relC =
  let ordObj = Map.toList $ foldr orderByClass Map.empty (Map.toList inst)
  in mapFilterJust $ foldr ((:) . getNoConfusionBSetsAxiom ordObj relC) [] ordObj

getNoConfusionBSetsAxiom :: [(TypeClass, [String])] -> Rel.Rel TypeClass ->
                            (TypeClass, [String]) -> Maybe (Named CASLFORMULA)
getNoConfusionBSetsAxiom ordObj relC (tc, lisObj) =
  case lisObj of
    [] -> Nothing
    _ : _ ->
     let filteredObj = removeUntilType tc ordObj
         diffForm = foldr ((++) . diffOfRestConstants (tc, lisObj) relC)
                     [] filteredObj in
                   case diffForm of
                     [] -> Nothing
                     _ : _ -> let constr = Junction Con diffForm nullRange
                              in Just $ makeNamed ("noConfusion_" ++ name tc) constr

removeUntilType :: TypeClass -> [(TypeClass, [String])] -> [(TypeClass, [String])]
removeUntilType tc lis =
  case lis of
    [] -> []
    (tc2, lisObj2) : rest -> if tc == tc2
                            then (tc2, lisObj2) : rest
                            else removeUntilType tc rest

diffOfRestConstants :: (TypeClass, [String]) -> Rel.Rel TypeClass ->
                       (TypeClass, [String]) -> [CASLFORMULA]
diffOfRestConstants (tc1, lisObj1) relC (tc2, lisObj2)
  | tc1 == tc2 = foldr ((++) . diffOfRestOps tc1 lisObj1) [] lisObj1
  | haveCommonSort tc1 tc2 relC =
     concatMap (diffOfRestOpsDiffSort (tc1, lisObj1) tc2) lisObj2
  | otherwise = []

haveCommonSort :: TypeClass -> TypeClass -> Rel.Rel TypeClass -> Bool
haveCommonSort t1 t2 relT =
  let succT1 = superSorts relT t1
      succT2 = superSorts relT t2
  in not $ Set.null $ Set.intersection succT1 succT2

-- This is the non exported function reachable in Rel
superSorts :: Rel.Rel TypeClass -> TypeClass -> Set.Set TypeClass
superSorts relT tc = Set.fold reach Set.empty $ Rel.succs relT tc where
         reach e s = if Set.member e s then s
                     else Set.fold reach (Set.insert e s) $ Rel.succs relT e


diffOfRestOpsDiffSort :: (TypeClass, [String]) -> TypeClass -> String -> [CASLFORMULA]
diffOfRestOpsDiffSort (tc1, lisObj1) tc2 objName = concatMap
 (diffOpsDiffSorts tc2 objName tc1) lisObj1

diffOpsDiffSorts :: TypeClass -> String -> TypeClass -> String -> [CASLFORMULA]
diffOpsDiffSorts tc2 objName2 tc1 objName1 =
  [Negation (Equation (Application (Qual_op_name (stringToId objName1)
    (Op_type Total [] (stringToId $ name tc1) nullRange) nullRange) [] nullRange)
    Strong (Application (Qual_op_name (stringToId objName2)
            (Op_type Total [] (stringToId $ name tc2) nullRange)
      nullRange) [] nullRange) nullRange) nullRange]


diffOfRestOps :: TypeClass -> [String] -> String -> [CASLFORMULA]
diffOfRestOps tc lisObj objName =
  let lis = removeUntil lisObj objName
  in concatMap (diffOps tc objName) lis

removeUntil :: [String] -> String -> [String]
removeUntil lis str =
  case lis of
    [] -> []
    a : rest -> if a == str
                then rest
                else removeUntil rest str

diffOps :: TypeClass -> String -> String -> [CASLFORMULA]
diffOps tc objName1 objName2 =
      [Negation (Equation
                 (Application (Qual_op_name (stringToId objName1)
                        (Op_type Total [] (stringToId $ name tc) nullRange)
                        nullRange) [] nullRange)
                 Strong
                 (Application (Qual_op_name (stringToId objName2)
                        (Op_type Total [] (stringToId $ name tc) nullRange)
                        nullRange) [] nullRange)
                 nullRange)
       nullRange | objName1 /= objName2]

toSortConstraint :: (TypeClass, [String]) -> Named CASLFORMULA
toSortConstraint (tc, lisObj) =
  let
    sor = stringToId $ name tc
    simplCon = Constraint sor (foldr ((:) . toConstraint sor) [] lisObj) sor
    constr = mkSort_gen_ax [simplCon] True
  in
    makeNamed ("sortGenCon_" ++ name tc) constr


toConstraint :: Id -> String -> (OP_SYMB, [Int])
toConstraint sor obName =
  let obj = stringToId obName
  in
    (Qual_op_name obj (Op_type Total [] sor nullRange) nullRange, [])


-- Each abstract class is the disjoint embedding of it subsorts
disjointEmbedding :: Set.Set TypeClass -> Rel.Rel TypeClass ->
                     [Named CASLFORMULA]
disjointEmbedding absCl rel =
  let
      injSyms = map (\ (s, t) -> (Qual_op_name
        (mkUniqueInjName (stringToId $ name s) (stringToId $ name t))
       (Op_type Total [stringToId $ name s]
        (stringToId $ name t) nullRange) nullRange, [])) $ Rel.toList $
       Rel.irreflex rel
      resType _ (Op_name _, _) = False
      resType s (Qual_op_name _ t _, _) = res_OP_TYPE t == s
      collectOps s = Constraint (stringToId $ name s)
       (filter (resType (stringToId $ name s)) injSyms) (stringToId $ name s)
      sortList = Set.toList absCl
      constrs = map collectOps sortList
  in
      [makeNamed "disjEmbedd" (Sort_gen_ax constrs True)]


mapSen :: CASLSign -> CSMOF.Sen -> CASLFORMULA
mapSen sig (Sen con car cot) = -- trueForm
   case cot of
     EQUAL -> let
                minC = minConstraint con car (predMap sig)
                maxC = maxConstraint con car (predMap sig)
              in
                Junction Con (minC : [maxC]) nullRange
     LEQ -> maxConstraint con car (predMap sig)
     GEQ -> minConstraint con car (predMap sig)


minConstraint :: MultConstr -> Integer -> PredMap -> CASLFORMULA
minConstraint con int predM =
  let
    predTypes = MapSet.lookup (stringToId $ getRole con) predM -- Set PredType
    souVars = generateVars "x" 1
    tarVars = generateVars "y" int
    correctPredType = Set.fold (getCorrectPredType con) [] predTypes
    souVarDec = Var_decl souVars (head (predArgs (head correctPredType))) nullRange
    tarVarDec = Var_decl tarVars (last (predArgs (head correctPredType))) nullRange
  in
    if int > 1
    then Quantification Universal [souVarDec] (Quantification
          Existential [tarVarDec] (Junction Con (generateVarDiff tarVarDec :
            [generateProp souVarDec tarVarDec (stringToId $ getRole con)])
             nullRange) nullRange) nullRange
    else Quantification Universal [souVarDec] (Quantification
          Existential [tarVarDec] (generateProp souVarDec tarVarDec
            (stringToId $ getRole con)) nullRange) nullRange

getCorrectPredType :: MultConstr -> PredType -> [PredType] -> [PredType]
getCorrectPredType con pt ptLis =
   if stringToId (name (CSMOF.getType con)) == head (predArgs pt)
   then pt : ptLis else ptLis

generateVars :: String -> Integer -> [VAR]
generateVars varRoot int =
  case int of
    1 -> [mkSimpleId (varRoot ++ "_" ++ show int)]
    n -> mkSimpleId (varRoot ++ "_" ++ show int) : generateVars varRoot (n - 1)

generateVarDiff :: VAR_DECL -> CASLFORMULA
generateVarDiff (Var_decl vars sor _) = Junction Con
 (foldr ((++) . diffOfRest sor vars) [] vars) nullRange

diffOfRest :: SORT -> [VAR] -> VAR -> [CASLFORMULA]
diffOfRest sor vars var = map (diffVar sor var) vars

diffVar :: SORT -> VAR -> VAR -> CASLFORMULA
diffVar sor var1 var2 =
  if var1 /= var2
  then Negation (Equation
                 (Qual_var var1 sor nullRange)
                 Strong
                 (Qual_var var2 sor nullRange)
                 nullRange)
       nullRange
  else trueForm

generateProp :: VAR_DECL -> VAR_DECL -> Id -> CASLFORMULA
generateProp (Var_decl varD sort _) (Var_decl varD2 sort2 _) rol =
  Junction Con (map (createPropRel (head varD) sort rol sort2) varD2) nullRange

createPropRel :: VAR -> SORT -> Id -> SORT -> VAR -> CASLFORMULA
createPropRel souVar sor rol sor2 tarVar =
  Predication (C.Qual_pred_name rol (Pred_type [sor, sor2] nullRange) nullRange)
    (Qual_var souVar sor nullRange : [Qual_var tarVar sor2 nullRange]) nullRange


maxConstraint :: MultConstr -> Integer -> PredMap -> CASLFORMULA
maxConstraint con int predM =
  let
    predTypes = MapSet.lookup (stringToId $ getRole con) predM -- Set PredType
    souVars = generateVars "x" 1
    tarVars = generateVars "y" (int + 1)
    correctPredType = Set.fold (getCorrectPredType con) [] predTypes
    souVarDec = Var_decl souVars (head (predArgs (head correctPredType))) nullRange
    tarVarDec = Var_decl tarVars (last (predArgs (head correctPredType))) nullRange
  in
    Quantification Universal (souVarDec : [tarVarDec])
                   (Relation
                      (Junction Con [generateProp souVarDec tarVarDec (stringToId $ getRole con)] nullRange)
                      Implication
                      (Junction Dis (generateExEqual tarVarDec) nullRange)
                      nullRange)
                   nullRange

generateExEqual :: VAR_DECL -> [CASLFORMULA]
generateExEqual (Var_decl varD sor _) = generateExEqualList varD sor

generateExEqualList :: [VAR] -> SORT -> [CASLFORMULA]
generateExEqualList vars sor =
  case vars of
    [] -> []
    v : rest -> generateExEqualVar rest sor v ++ generateExEqualList rest sor

generateExEqualVar :: [VAR] -> SORT -> VAR -> [CASLFORMULA]
generateExEqualVar vars sor var =
  foldr ((++) . (\ el -> if el == var
                then []
                else [Equation (Qual_var var sor nullRange) Strong
                       (Qual_var el sor nullRange) nullRange]))
        [] vars


-- | Translation of morphisms
mapMor :: CSMOF.Morphism -> Result CASLMor
mapMor m = return C.Morphism
  { msource = mapSign $ domOfDefaultMorphism m
  , mtarget = mapSign $ codOfDefaultMorphism m
  , sort_map = Map.empty
  , op_map = Map.empty
  , pred_map = Map.empty
  , extended_map = ()
  }


-- mapSym :: CSMOF.Symbol -> C.Symbol

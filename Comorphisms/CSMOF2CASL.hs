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
    ( CSMOF2CASL (..)
    ) where

import Logic.Logic
import Logic.Comorphism

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
-- import CASL.Fold
-- import CASL.Overload

import Common.AS_Annotation
import Common.GlobalAnnotations
-- import Common.DefaultMorphism
-- import Common.DocUtils
import Common.Id
import Common.ProofTree
import Common.Result
-- import Common.Token
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
-- import Common.Lib.State

import qualified Data.Set as Set
import qualified Data.Map as Map

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
        , cons_features = SortGen False True }
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
    preds = getPredicates (properties s)
    sent = getSentencesRels (links s) 
    sentDisEmb = getSortGen (typeRel s) (abstractClasses s) (instances s)
  in
    C.Sign
    { sortRel = sorts
    , revSortRel = Just $ Rel.fromList (map revertOrder (Rel.toList sorts))
    , emptySortSet = Set.empty
    , opMap = ops
    , assocOps = MapSet.empty
    , predMap = fst preds
    , varMap = Map.empty
    , sentences = snd preds ++ sent ++ sentDisEmb
    , declaredSymbols = Set.empty
    , envDiags = []
    , annoMap = MapSet.empty
    , globAnnos = emptyGlobalAnnos
    , extendedInfo = ()
    }

getSorts :: Set.Set TypeClass -> Rel.Rel TypeClass -> Rel.Rel SORT
getSorts setC relC = 
  let relS = Set.fold (insertSort . name) Rel.empty setC
  in foldr (insertPair) relS (Rel.toList relC)

insertSort :: String -> Rel.Rel SORT -> Rel.Rel SORT
insertSort s relS = Rel.insertPair (stringToId s) (stringToId s) relS

insertPair :: (TypeClass,TypeClass) -> Rel.Rel SORT -> Rel.Rel SORT
insertPair (t1,t2) relS = Rel.insertPair (stringToId $ name t1) (stringToId $ name t2) relS

revertOrder :: (SORT,SORT) -> (SORT,SORT)
revertOrder (a,b) = (b,a)

getPredicates :: Set.Set PropertyT -> (PredMap,[Named (FORMULA f)])
getPredicates props = Set.fold (insertPredicate) (MapSet.empty,[]) props

insertPredicate :: PropertyT -> (PredMap,[Named (FORMULA f)]) -> (PredMap,[Named (FORMULA f)])
insertPredicate prop (predM,form) = 
  let 
    sort1 = stringToId $ name $ sourceType prop
    sort2 = stringToId $ name $ targetType prop
    pname1 = stringToId $ targetRole prop
    ptype1 = PredType $ sort1 : [sort2]
    pname2 = stringToId $ sourceRole prop
    ptype2 = PredType $ sort2 : [sort1]
    nam = "equiv_" ++ targetRole prop ++ "_" ++ sourceRole prop
    sent = C.Relation 
             (C.Predication (C.Pred_name pname2) 
                          (C.Qual_var (mkSimpleId "x") sort2 nullRange : [C.Qual_var (mkSimpleId "y") sort1 nullRange]) 
                          nullRange) 
             C.Equivalence 
             (C.Predication (C.Pred_name pname1) 
                          (C.Qual_var (mkSimpleId "y") sort1 nullRange : [C.Qual_var (mkSimpleId "x") sort2 nullRange]) 
                          nullRange) 
             nullRange
  in 
    -- MapSet does not allows repeated elements, but predicate names can be repeated 
    -- (this must be corrected by creating a more complex ID)
    if sourceRole prop == "_" 
    then (MapSet.insert pname1 ptype1 predM, form)
    else if targetRole prop == "_" 
         then (MapSet.insert pname2 ptype2 predM, form)
         else (MapSet.insert pname1 ptype1 $ MapSet.insert pname2 ptype2 predM, (makeNamed nam sent) : form)


getOperations :: Map.Map String TypeClass -> OpMap
getOperations ops = foldr (insertOperations) MapSet.empty (Map.toList ops)

insertOperations :: (String,TypeClass) -> OpMap -> OpMap
insertOperations (na,tc) opM = 
  let
    opName = stringToId na
    opType = OpType Total [] (stringToId $ name tc)
  in 
    MapSet.insert opName opType opM


getSentencesRels :: Set.Set LinkT -> [Named (CASLFORMULA)]
getSentencesRels linkk = completenessOfRelations linkk


completenessOfRelations :: Set.Set LinkT -> [Named (CASLFORMULA)]
completenessOfRelations linkk =
  let ordLinks = getLinksByProperty linkk
  in foldr ((++) . createComplFormula) [] (Map.toList ordLinks)

createComplFormula ::  (String,[LinkT]) -> [Named (CASLFORMULA)]
createComplFormula (nam,linksL) = 
  let
    varA = mkSimpleId "x"
    varB = mkSimpleId "y"
  in
    case linksL of
      [] -> []
      (LinkT _ _ pr) : _ -> let
                                   sorA = stringToId $ name $ sourceType pr
                                   sorB = stringToId $ name $ targetType pr
                                   sent = C.Relation 
                                             (C.Predication (C.Pred_name (stringToId $ targetRole pr)) 
                                                (C.Qual_var varA sorA nullRange 
                                                   : [C.Qual_var varB sorB nullRange]) 
                                                 nullRange) 
                                             C.Equivalence 
                                             (Junction Dis (foldr ((:) . (getPropHold varA sorA varB sorB)) [] linksL) nullRange) 
                                             nullRange
                                 in
                                   [makeNamed ("compRel_" ++ nam) sent]

getPropHold :: VAR -> SORT -> VAR -> SORT -> LinkT -> CASLFORMULA
getPropHold varA sorA varB sorB lin = 
  let
    eqA = Equation (Qual_var varA sorA nullRange) 
                   Strong 
                   (Qual_var (mkSimpleId (sourceVar lin)) (stringToId $ name $ sourceType (property lin)) nullRange) 
                   nullRange
    eqB = Equation (Qual_var varB sorB nullRange) 
                   Strong 
                   (Qual_var (mkSimpleId (targetVar lin)) (stringToId $ name $ targetType (property lin)) nullRange) 
                   nullRange
  in
    Junction Con (eqA : [eqB]) nullRange


getLinksByProperty :: Set.Set LinkT -> Map.Map String [LinkT]
getLinksByProperty linkk = 
  let elems = Set.elems linkk
  in foldr (getByProperty) Map.empty elems

getByProperty :: LinkT -> Map.Map String [LinkT] -> Map.Map String [LinkT]
getByProperty lin mapL = 
  let 
    prope = CSMOF.property lin
    nameLook = sourceRole prope ++ name (sourceType prope) ++ targetRole prope ++ name (targetType prope)
    setProp = Map.lookup nameLook mapL
  in 
    case setProp of
      Nothing -> Map.insert nameLook [lin] (Map.delete nameLook mapL)
      Just s -> Map.insert nameLook (lin : s) (Map.delete nameLook mapL)


getSortGen :: Rel.Rel TypeClass -> Set.Set TypeClass -> Map.Map String TypeClass -> [Named (CASLFORMULA)]
getSortGen typpR absCl inst = 
  disjointEmbedding absCl typpR ++ sortGeneration inst

-- Sorts are generated as a free type of object functions
sortGeneration :: Map.Map String TypeClass -> [Named (CASLFORMULA)]
sortGeneration inst = 
  let ordObj = foldr (orderByClass) Map.empty (Map.toList inst)
  in foldr ((:) . toSortConstraint) [] (Map.toList ordObj)

orderByClass :: (String,TypeClass) -> Map.Map TypeClass [String] -> Map.Map TypeClass [String]
orderByClass (ob,tc) mapTC = 
  case Map.lookup tc mapTC of
    Nothing -> Map.insert tc [ob] mapTC
    Just listObj -> Map.insert tc (ob : listObj) (Map.delete tc mapTC)

toSortConstraint :: (TypeClass, [String]) -> Named (CASLFORMULA)
toSortConstraint (tc,lisObj) = 
  let 
    sor = stringToId $ name tc
    simplCon = Constraint sor (foldr ((:) . toConstraint sor) [] lisObj) sor
    constr = Sort_gen_ax [simplCon] True
  in 
    makeNamed ("sortGenCon_" ++ name tc) constr

--  let constr = Sort_gen_ax (foldr ((:) . toConstraint tc) [] lisObj) True
--  in makeNamed ("sortGenCon_" ++ name tc) constr

toConstraint :: Id -> String -> (OP_SYMB, [Int])
toConstraint sor obName =
  let obj = stringToId obName
  in
    (Qual_op_name obj (Op_type Total [] sor nullRange) nullRange,[])


-- Each abstract class is the disjoint embedding of it subsorts
disjointEmbedding :: Set.Set TypeClass -> Rel.Rel TypeClass -> [Named (CASLFORMULA)]
disjointEmbedding absCl rel =
  let injSyms = map (\ (s, t) -> (Qual_op_name (mkUniqueInjName (stringToId $ name s) (stringToId $ name t))
                                   (Op_type Total [(stringToId $ name s)] (stringToId $ name t) nullRange) nullRange,[]))
                     $ Rel.toList
                     $ Rel.irreflex rel
      resType _ ((Op_name _),_) = False
      resType s ((Qual_op_name _ t _),_) = res_OP_TYPE t == s
      collectOps s = Constraint (stringToId $ name s) (filter (resType (stringToId $ name s)) injSyms) (stringToId $ name s)
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
    predTypes = Set.elems $ MapSet.lookup (stringToId $ getRole con) predM -- [PredType]
    souVars = generateVars "x" 1
    tarVars = generateVars "y" int
    souVarDec = Var_decl souVars (head (predArgs (head predTypes))) nullRange
    tarVarDec = Var_decl tarVars (last (predArgs (head predTypes))) nullRange
  in 
    if int > 1
    then Quantification Universal [souVarDec] (Quantification 
                                      Existential 
                                      [tarVarDec] 
                                      (Junction Con ((generateVarDiff tarVarDec) : 
                                         [(generateProp souVarDec tarVarDec (stringToId $ getRole con))]) nullRange)
                                       nullRange) 
                                  nullRange
    else Quantification Universal [souVarDec] (Quantification 
                                      Existential 
                                      [tarVarDec] 
                                      (generateProp souVarDec tarVarDec (stringToId $ getRole con))
                                      nullRange
                                     ) nullRange


generateVars :: String -> Integer -> [VAR]
generateVars varRoot int =
  case int of
    1 -> [mkSimpleId (varRoot ++ "_" ++ show int)]
    n -> mkSimpleId (varRoot ++ "_" ++ show int) : generateVars varRoot (n-1)

generateVarDiff :: VAR_DECL -> CASLFORMULA
generateVarDiff (Var_decl vars sor _) = Junction Con (foldr ((++) . diffOfRest sor vars) [] vars) nullRange

diffOfRest :: SORT -> [VAR] -> VAR -> [CASLFORMULA]
diffOfRest sor vars var = map (diffVar sor var) vars

diffVar :: SORT -> VAR -> VAR -> CASLFORMULA
diffVar sor var1 var2 = 
  if not (var1 == var2) 
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
  Predication (C.Pred_name rol) 
    ((Qual_var souVar sor nullRange):[Qual_var tarVar sor2 nullRange]) nullRange


maxConstraint :: MultConstr -> Integer -> PredMap -> CASLFORMULA
maxConstraint con int predM = 
  let 
    predTypes = Set.elems $ MapSet.lookup (stringToId $ getRole con) predM -- [PredType]
    souVars = generateVars "x" 1
    tarVars = generateVars "y" (int + 1)
    souVarDec = Var_decl souVars (head (predArgs (head predTypes))) nullRange
    tarVarDec = Var_decl tarVars (last (predArgs (head predTypes))) nullRange
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
    v : rest ->  (generateExEqualVar rest sor v) ++ (generateExEqualList rest sor)

generateExEqualVar :: [VAR] -> SORT -> VAR -> [CASLFORMULA]
generateExEqualVar vars sor var = 
  foldr ((++) . (\el -> if el == var 
                then [] 
                else [Equation (Qual_var var sor nullRange) Strong (Qual_var el sor nullRange) nullRange]))
        [] vars



-- | Translation of morphisms
mapMor :: CSMOF.Morphism -> Result CASLMor
mapMor _ = return C.Morphism
  { msource = C.emptySign ()
  , mtarget = C.emptySign ()
  , sort_map = Map.empty
  , op_map = Map.empty
  , pred_map = Map.empty
  , extended_map = ()
  }


-- mapSym :: CSMOF.Symbol -> C.Symbol




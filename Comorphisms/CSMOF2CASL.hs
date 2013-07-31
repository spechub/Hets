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
        , cons_features = NoSortGen }
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
  return (cs, map (mapNamed $ mapSen cs) ns)


mapSign :: CSMOF.Sign -> CASLSign
mapSign s = 
  let 
    sorts = getSorts (types s) (typeRel s)
    ops = getOperations (instances s)
    preds = getPredicates (properties s)
    sent = getSentences (typeRel s) (links s) (abstractClasses s)
  in
    C.Sign
    { sortRel = sorts
    , revSortRel = Just $ Rel.fromList (map revertOrder (Rel.toList sorts))
    , emptySortSet = Set.empty
    , opMap = ops
    , assocOps = MapSet.empty
    , predMap = fst preds
    , varMap = Map.empty
    , sentences = snd preds ++ sent
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
insertSort s relS = Rel.insertPair (mkInfix s) (mkInfix s) relS

insertPair :: (TypeClass,TypeClass) -> Rel.Rel SORT -> Rel.Rel SORT
insertPair (t1,t2) relS = Rel.insertPair (mkInfix $ name t1) (mkInfix $ name t2) relS

revertOrder :: (SORT,SORT) -> (SORT,SORT)
revertOrder (a,b) = (b,a)

getPredicates :: Set.Set PropertyT -> (PredMap,[Named (FORMULA f)])
getPredicates props = Set.fold (insertPredicate) (MapSet.empty,[]) props

insertPredicate :: PropertyT -> (PredMap,[Named (FORMULA f)]) -> (PredMap,[Named (FORMULA f)])
insertPredicate prop (predM,form) = 
  let 
    sort1 = mkInfix $ name $ sourceType prop
    sort2 = mkInfix $ name $ targetType prop
    pname1 = mkInfix $ targetRole prop
    ptype1 = PredType $ sort1 : [sort2]
    pname2 = mkInfix $ sourceRole prop
    ptype2 = PredType $ sort2 : [sort1]
    nam = "equiv_" ++ targetRole prop ++ "_" ++ sourceRole prop
    sent = C.Relation 
             (C.Predication (C.Pred_name pname1) 
                          (C.Qual_var (mkSimpleId "x") sort2 nullRange : [C.Qual_var (mkSimpleId "y") sort1 nullRange]) 
                          nullRange) 
             C.Equivalence 
             (C.Predication (C.Pred_name pname2) 
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
    opName = mkInfix na
    opType = OpType Total [] (mkInfix $ name tc)
  in 
    MapSet.insert opName opType opM


getSentences :: Rel.Rel TypeClass -> Set.Set LinkT -> Set.Set TypeClass -> [Named (FORMULA f)]
getSentences _ _ _ = [] -- relC setL setT = ???
--  if an abstract class then is the disjoint embedding of subsorts (free type)
--      Sort_gen_ax [Constraint] True
--           Constraint newSort [(OP_SYMB, [Int])] origSort
-- for each link, the corresponding predicate holds
-- sorts are generated as a free type of object functions
-- predicate iff each case of link (completeness of relations)


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
    predTypes = Set.elems $ MapSet.lookup (mkInfix $ getRole con) predM -- [PredType]
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
                                         [(generateProp souVarDec tarVarDec (mkInfix $ getRole con))]) nullRange)
                                       nullRange) 
                                  nullRange
    else Quantification Universal [souVarDec] (Quantification 
                                      Existential 
                                      [tarVarDec] 
                                      (generateProp souVarDec tarVarDec (mkInfix $ getRole con))
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
    predTypes = Set.elems $ MapSet.lookup (mkInfix $ getRole con) predM -- [PredType]
    souVars = generateVars "x" 1
    tarVars = generateVars "y" (int + 1)
    souVarDec = Var_decl souVars (head (predArgs (head predTypes))) nullRange
    tarVarDec = Var_decl tarVars (last (predArgs (head predTypes))) nullRange
  in 
    Quantification Universal (souVarDec : [tarVarDec]) 
                   (Relation 
                      (Junction Con [generateProp souVarDec tarVarDec (mkInfix $ getRole con)] nullRange)
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




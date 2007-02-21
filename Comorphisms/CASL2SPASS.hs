{- |
Module      :  $Header$
Description :  Coding of CASL into SoftFOL
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from CASL to SoftFOL.
-}

{- todo

   - elimination of single sorts is only possible while generating
     DFG or TPTP, mark the Sort/set the flag

   - implement translation of Sort_gen_ax (FORMULA f) as goals
     (s. below for a sketch) .. Klaus Lüttich
-}

module Comorphisms.CASL2SPASS
    (SuleCFOL2SoftFOL(..), SuleCFOL2SoftFOLInduction(..))
    where

-- Debuging and Warning
import Debug.Trace
import Control.Exception

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import Data.List as List
import Data.Maybe

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import qualified CASL.Sign as CSign
import CASL.Morphism
import CASL.Quantification
import CASL.Overload
import CASL.Utils
import CASL.Inject
import CASL.Induction (generateInductionLemmas)

-- SoftFOL
import SPASS.Sign as SPSign
import SPASS.Logic_SPASS
import SPASS.Translate
import SPASS.Utils

-- | The identity of the comorphisms
data SuleCFOL2SoftFOL = SuleCFOL2SoftFOL deriving (Show)
data SuleCFOL2SoftFOLInduction = SuleCFOL2SoftFOLInduction deriving (Show)

-- | SoftFOL theories
type SoftFOLTheory = (SPSign.Sign,[Named SPTerm])

-- | CASL Ids with Types mapped to SPIdentifier
type IdType_SPId_Map = Map.Map Id (Map.Map CType SPIdentifier)

-- | specialized lookup for IdType_SPId_Map
lookupSPId :: Id -> CType -> IdType_SPId_Map ->
          Maybe SPIdentifier
lookupSPId i t m = maybe Nothing (\ m' -> Map.lookup t m') (Map.lookup i m)

-- | specialized insert (with error) for IdType_SPId_Map
insertSPId :: Id -> CType ->
              SPIdentifier ->
              IdType_SPId_Map ->
              IdType_SPId_Map
insertSPId i t spid m =
    assert (checkIdentifier t spid) $
    Map.insertWith (Map.unionWith err) i (Map.insert t spid Map.empty) m
    where err = error ("SuleCFOL2SoftFOL: for Id \""++show i ++
                       "\" the type \""++ show t ++
                       "\" can't be mapped to different SoftFOL identifiers")

deleteSPId :: Id -> CType ->
              IdType_SPId_Map ->
              IdType_SPId_Map
deleteSPId i t m =
    maybe m (\ m2 -> let m2' = Map.delete t m2
                     in if Map.null m2'
                           then Map.delete i m
                           else Map.insert i m2' m) $
          Map.lookup i m

-- | specialized elems into a set for IdType_SPId_Map
elemsSPId_Set :: IdType_SPId_Map -> Set.Set SPIdentifier
elemsSPId_Set = Map.fold (\ m res -> Set.union res
                                      (Set.fromList (Map.elems m)))
                         Set.empty



-- extended signature translation
type SignTranslator f e = CSign.Sign f e -> e -> SoftFOLTheory -> SoftFOLTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e =
    CSign.Sign f e -> IdType_SPId_Map -> f -> SPTerm

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "SuleCFOL2SoftFOL: No extended formulas allowed in CASL"

instance Language SuleCFOL2SoftFOL -- default definition is okay
instance Language SuleCFOL2SoftFOLInduction -- default definition is okay

instance Comorphism SuleCFOL2SoftFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol ()
               SoftFOL () () SPTerm () ()
               SPSign.Sign
               SoftFOLMorphism () () SPSign.ATP_ProofTree where
    sourceLogic _ = CASL
    sourceSublogic _ = SL.top
                      { sub_features = LocFilSub,
                        has_part = False,
                        cons_features = SortGen { emptyMapping = True,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic _ = SoftFOL
    mapSublogic _ _ = ()
    map_theory _ = transTheory sigTrCASL formTrCASL
    map_morphism = mapDefaultMorphism
    map_sentence _ sign =
      return . mapSen (isSingleSorted sign) formTrCASL sign
    map_symbol = errMapSymbol

instance Comorphism SuleCFOL2SoftFOLInduction
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol ()
               SoftFOL () () SPTerm () ()
               SPSign.Sign
               SoftFOLMorphism () () SPSign.ATP_ProofTree where
    sourceLogic _ = CASL
    sourceSublogic _ = SL.top
                      { sub_features = LocFilSub,
                        has_part = False,
                        cons_features = SortGen { emptyMapping = True,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic _ = SoftFOL
    mapSublogic _ _ = ()
    map_theory _ = transTheory sigTrCASL formTrCASL . generateInductionLemmas
    map_morphism = mapDefaultMorphism
    map_sentence _ sign =
      return . mapSen (isSingleSorted sign) formTrCASL sign
    map_symbol = errMapSymbol

---------------------------- Signature -----------------------------

transFuncMap :: IdType_SPId_Map ->
                CSign.Sign e f ->
                (FuncMap, IdType_SPId_Map)
transFuncMap idMap sign =
    Map.foldWithKey toSPOpType (Map.empty,idMap) (CSign.opMap sign)
    where toSPOpType iden typeSet (fm,im) =
              if Set.null typeSet then
                  error ("SuleCFOL2SoftFOL: empty sets are not "++
                         "allowed in OpMaps: " ++ show iden)
              else if Set.null $ Set.deleteMin typeSet then
                 let oType = Set.findMin typeSet
                     sid' = sid fm oType
                 in (Map.insert sid' (Set.singleton (transOpType oType)) fm,
                      insertSPId iden (COp oType) sid' im)
              else Set.fold insOIdSet (fm,im) $
                         partOverload (leqF sign)
                           (partArities (length . CSign.opArgs) typeSet)
              where insOIdSet tset (fm',im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transOpType tset) fm',
                            Set.fold (\ x y ->
                                          insertSPId iden (COp x) sid' y)
                                     im' tset)
                    sid fma t = disSPOId (COp t) (transId (COp t) iden)
                                       (uType (transOpType t))
                                       (Set.union (Rel.keysSet fma)
                                           (elemsSPId_Set idMap))
                    uType t = fst t ++ [snd t]

-- 1. devide into sets with different arities
partArities :: (Ord a) => (a -> Int) -> Set.Set a -> Set.Set (Set.Set a)
partArities len = part 0 Set.empty
    where part i acc s
              | Set.null s = acc
              | otherwise =
                  case Set.partition (\ x -> len x == i) s of
                  (ar_i,rest) ->
                      part (i+1) (if Set.null ar_i
                                  then acc
                                  else Set.insert ar_i acc) rest

partOverload :: (Show a,Ord a) => (a -> a -> Bool)
             -> Set.Set (Set.Set a)
             -> Set.Set (Set.Set a)
partOverload leq = Set.fold part Set.empty
    where part s = Set.union (Set.fromList $ Rel.partSet leq s)

transPredMap :: IdType_SPId_Map ->
                CSign.Sign e f ->
                (PredMap, IdType_SPId_Map)
transPredMap idMap sign =
    Map.foldWithKey toSPPredType (Map.empty,idMap) (CSign.predMap sign)
    where toSPPredType iden typeSet (fm,im) =
              if Set.null typeSet then
                  error ("SuleCFOL2SoftFOL: empty sets are not "++
                         "allowed in PredMaps: " ++ show iden)
              else if Set.null $ Set.deleteMin typeSet then
                let pType = Set.findMin typeSet
                    sid' = sid fm pType
                in (Map.insert sid' (Set.singleton (transPredType pType)) fm,
                      insertSPId iden (CPred pType) sid' im)
              else Set.fold insOIdSet (fm,im) $
                         partOverload (leqP sign)
                            (partArities (length . CSign.predArgs) typeSet)

              where insOIdSet tset (fm',im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transPredType tset) fm',
                            Set.fold (\ x y ->
                                          insertSPId iden (CPred x) sid' y)
                                     im' tset)
                    sid fma t = disSPOId (CPred t) (transId (CPred t) iden)
                                       (transPredType t)
                                       (Set.union (Rel.keysSet fma)
                                           (elemsSPId_Set idMap))
-- | disambiguation of SPASS Identifiers
disSPOId :: CType -- ^ Type of CASl identifier
         -> SPIdentifier -- ^ translated CASL Identifier
         -> [SPIdentifier] -- ^ translated Sort Symbols of the profile
                           -- (maybe empty)
         -> Set.Set SPIdentifier -- ^ SPASS Identifiers already in use
         -> SPIdentifier -- ^ fresh Identifier generated from second argument;
    -- if the identifier was not in the set this is just the second argument
disSPOId cType sid ty idSet
    | checkIdentifier cType sid && not (lkup sid) = sid
    | otherwise = let nSid = disSPOId' sid
                  in assert (checkIdentifier cType nSid) nSid
    where disSPOId' sid'
              | not (lkup asid) = asid
              | otherwise = addType asid 1
              where asid = sid' ++ case cType of
                        CSort  -> ""
                        CVar _ -> ""
                        x -> '_':show (length ty - (case x of
                                                    COp _ -> 1
                                                    _     -> 0))
                    addType res n =
                        let nres = asid ++ '_':fc n
                            nres' = nres ++ '_':show n
                        in if nres == res
                           then if nres' == res
                                then error ("SuleCFOL2SoftFOL: cannot calculate"
                                            ++ " unambigous id for "
                                            ++ sid ++ " with type " ++ show ty
                                            ++ " and nres = "++ nres
                                            ++ "\n with idSet "
                                            ++ show idSet)
                                else if not (lkup nres')
                                     then nres'
                                     else addType nres (n+1)
                           else if not (lkup nres)
                                then nres
                                else addType nres (n+1)

--          tr x = trace ("disSPOId: Input: "++show cType ++ ' ':show sid
--                        ++ ' ':show ty ++ "\n  Output: "++ show x) x
          lkup x = Set.member x idSet
          fc n = concatMap (take n) ty

transOpType :: CSign.OpType -> ([SPIdentifier],SPIdentifier)
transOpType ot = (map transIdSort (CSign.opArgs ot),
                  transIdSort (CSign.opRes ot))

transPredType :: CSign.PredType -> [SPIdentifier]
transPredType pt = map transIdSort (CSign.predArgs pt)

-- | translate every Id as Sort
transIdSort :: Id -> String
transIdSort = transId CSort

integrateGenerated :: (Pretty f, PosItem f) =>
                      IdType_SPId_Map -> [Named (FORMULA f)] ->
                      SPSign.Sign ->
                      Result (IdType_SPId_Map, SPSign.Sign, [Named SPTerm])
integrateGenerated idMap genSens sign
    | null genSens = return (idMap,sign,[])
    | otherwise =
      case partition isAxiom genSens of
      (genAxs,genGoals) ->
        case makeGenGoals idMap genGoals of
        (newPredsMap,idMap',goalsAndSentences) ->
          -- makeGens must not invent new sorts
          case makeGens idMap' genAxs of
          Result dias mv ->
            maybe (Result dias Nothing)
                  (\ (spSortMap_makeGens,newOpsMap,idMap'',exhaustSens) ->
                      let spSortMap' =
                            Map.union spSortMap_makeGens (SPSign.sortMap sign)
                      in assert (Map.size spSortMap' ==
                                    Map.size (SPSign.sortMap sign))
                             (Result dias
                                     (Just (idMap'',
                                            sign { sortMap = spSortMap'
                                                 , funcMap =
                                                     Map.union (funcMap sign)
                                                               newOpsMap
                                                 , predMap =
                                                     Map.union (predMap sign)
                                                               newPredsMap},
                                            mkInjSentences idMap' newOpsMap++
                                            goalsAndSentences++
                                            exhaustSens))))
                  mv

makeGenGoals :: IdType_SPId_Map -> [Named (FORMULA f)]
                -> (PredMap, IdType_SPId_Map, [Named SPTerm])
makeGenGoals idMap nfs
    | null nfs = (Map.empty,idMap,[])
    | otherwise =
        trace "SuleCFOL2SoftFOL: Warning: Sort_gen_ax as goals not implemented, yet."
                  (Map.empty,idMap,[])
{- implementation sketch:
   - invent new predicate P that is supposed to hold on
     every x in the (freely) generated sort.
   - generate formulas with this predicate for each constructor.
   - recursive constructors hold if the predicate holds on the variables
   - prove forall x . P(x)

  implementation is postponed as this translation does not produce
only one goal, but additional symbols, axioms and a goal
 -}

makeGens :: (Pretty f, PosItem f) =>
            IdType_SPId_Map -> [Named (FORMULA f)]
         -> Result (SortMap, FuncMap, IdType_SPId_Map,[Named SPTerm])
            -- ^ The list of SoftFOL sentences gives exhaustiveness for
            -- generated sorts with only constant constructors
makeGens idMap fs =
    case foldl makeGen (return (Map.empty,idMap,[],[])) fs of
    Result ds mv ->
        maybe (Result ds Nothing)
              (\ (opMap,idMap',pairs,exhaustSens) ->
                   Result ds
                      (Just (foldr (uncurry Map.insert)
                                   Map.empty pairs,
                             opMap,idMap',exhaustSens)))
              mv

makeGen :: (Pretty f, PosItem f) =>
           Result (FuncMap, IdType_SPId_Map,
                   [(SPIdentifier,Maybe Generated)],[Named SPTerm])
        -> Named (FORMULA f)
        -> Result (FuncMap, IdType_SPId_Map,
                   [(SPIdentifier,Maybe Generated)],[Named SPTerm])
makeGen r@(Result ods omv) nf =
    maybe (Result ods Nothing) process omv where
 process (oMap,iMap,rList,eSens) = case sentence nf of
  Sort_gen_ax constrs free ->
      if null mp then (case mapAccumL makeGenP (oMap,iMap,[]) srts of
                       ((oMap',iMap',eSens'),genPairs) ->
                          Result ods (Just (oMap',iMap',
                                            rList++genPairs,
                                            eSens++eSens')))
                 else mkError "Non injective sort mappings cannot \
                              \be translated to SoftFOL" (sentence nf)
      where (srts,ops,mp) = recover_Sort_gen_ax constrs
            hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot
            hasTheSort _ _ = error "SuleCFOL2SoftFOL.hasTheSort"
            mkGen = Just . Generated free . map fst
            makeGenP (opMap,idMap,exSens) s = ((newOpMap, newIdMap,
                                                exSens++eSen ops_of_s s),
                                        (s', mkGen cons))
                where ((newOpMap,newIdMap),cons) =
                          mapAccumL mkInjOp (opMap,idMap) ops_of_s
                      ops_of_s = List.filter (hasTheSort s) ops
                      s' = maybe (error "SuleCFOL2SoftFOL.makeGen: No mapping \
                                        \found for '"++show s++"'") id
                                 (lookupSPId s CSort idMap)
            eSen os s = if all nullArgs os
                        then [(emptyName (SPQuantTerm SPForall
                                            [typedVarTerm var $
                                             maybe (error "lookup failed")
                                                   id
                                                   (lookupSPId s (CSort) iMap)]
                                            (disj var os)))
                              {senName = newName s}]
                        else []
            disj v os = case map (\x -> mkEq (varTerm v)
                                        (varTerm $ transOP_SYMB iMap x) ) os of
                        [] -> error "CASL2SPASS: no constructors found"
                        [x] -> x
                        xs -> foldl1 mkDisj xs
            var = fromJust (find (\ x -> not (Set.member x usedIds))
                            ("X":["X"++show i | i <- [(1::Int)..]]))
            varTerm v = simpTerm (spSym v)
            newName s = "ga_exhaustive_generated_sort_"++(show $ pretty s)
            usedIds = elemsSPId_Set iMap
            nullArgs o = case o of
                         Qual_op_name _ (Op_type _ args _ _) _ -> null args
                         _ -> error "CASL2SPASS: wrong constructor"
  _ -> r

mkInjOp :: (FuncMap, IdType_SPId_Map)
        -> OP_SYMB
        -> ((FuncMap,IdType_SPId_Map),
            (SPIdentifier,([SPIdentifier],SPIdentifier)))
mkInjOp (opMap,idMap) qo@(Qual_op_name i ot _) =
    if i == injName && isNothing lsid
       then ((Map.insert i' (Set.singleton (transOpType ot')) opMap,
              insertSPId i (COp ot') i' idMap),
             (i', transOpType ot'))
       else ((opMap,idMap),
             (maybe err id lsid,
              transOpType ot'))
    where i' = disSPOId (COp ot') (transId (COp ot') i)
                        (utype (transOpType ot')) usedNames
          ot' = CSign.toOpType ot
          lsid = lookupSPId i (COp ot') idMap
          usedNames = Rel.keysSet opMap
          err = error ("SuleCFOL2SoftFOL.mkInjOp: Cannot find SPId for '"++
                       show qo++"'")
          utype t = fst t ++ [snd t]
mkInjOp _ _ = error "SuleCFOL2SoftFOL.mkInjOp: Wrong constructor!!"

mkInjSentences :: IdType_SPId_Map
               -> FuncMap
               -> [Named SPTerm]
mkInjSentences idMap = Map.foldWithKey genInjs []
    where genInjs k tset fs = Set.fold (genInj k) fs tset
          genInj k (args,res) fs =
              assert (length args == 1)
                     ((emptyName
                       (SPQuantTerm SPForall [typedVarTerm var (head args)]
                             (compTerm SPEqual
                                       [compTerm (spSym k)
                                                 [simpTerm (spSym var)],
                                        simpTerm (spSym var)])))
                     {senName = newName k (head args) res} : fs)
          var = fromJust (find (\ x -> not (Set.member x usedIds))
                          ("x":["x"++show i | i <- [(1::Int)..]]))
          newName o a r = "ga_"++o++'_':a++'_':r++"_id"
          usedIds = elemsSPId_Set idMap

{- |
  Translate a CASL signature into SoftFOL signatur 'SPASS.Sign.Sign'.
  Before translating, eqPredicate symbols where removed from signature.
-}
transSign :: CSign.Sign f e -> (SPSign.Sign, IdType_SPId_Map)
transSign sign = (SPSign.emptySign { sortRel =
                                 Rel.map transIdSort (CSign.sortRel sign)
                           , sortMap = spSortMap
                           , funcMap = fMap
                           , predMap = pMap
                           , singleSorted = isSingleSorted sign
                           },idMap'')
    where (spSortMap,idMap) =
            Set.fold (\ i (sm,im) ->
                          let sid = disSPOId CSort (transIdSort i)
                                       [take 20 (cycle "So")]
                                       (Rel.keysSet sm)
                          in (Map.insert sid Nothing sm,
                              insertSPId i CSort sid im))
                                        (Map.empty,Map.empty)
                                        (CSign.sortSet sign)
          (fMap,idMap') =  transFuncMap idMap  sign
          (pMap,idMap'') = transPredMap idMap' sign

nonEmptySortSens :: SortMap -> [Named SPTerm]
nonEmptySortSens =
    Map.foldWithKey (\ s _ res -> extSen s:res) []
    where extSen s =
              (emptyName (SPQuantTerm SPExists [varTerm]
                                    (compTerm (spSym s) [varTerm])))
              {senName = "ga_non_empty_sort_"++s}
              where varTerm = simpTerm (spSym (newVar s))
          newVar s = fromJust (find (\ x -> x /= s)
                          ("X":["X"++show i | i <- [(1::Int)..]]))


transTheory :: (Pretty f, PosItem f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result SoftFOLTheory
transTheory trSig trForm (sign,sens) =
  fmap (trSig sign (CSign.extendedInfo sign))
    (case transSign (filterPreds $ foldl insInjOps sign genAxs) of
     (tSign,idMap) ->
        do (idMap',tSign',sentencesAndGoals) <-
               integrateGenerated idMap genSens tSign
           let tSignElim = if SPSign.singleSortNotGen tSign'
                             then tSign' {sortMap = Map.empty} else tSign'
           return  (tSignElim,
                    sentencesAndGoals ++
                    nonEmptySortSens (sortMap tSignElim) ++
                    map (mapNamed (transFORM (singleSortNotGen tSign') eqPreds
                                     sign idMap' trForm))
                        realSens'))

  where (genSens,realSens) =
            partition (\ s -> case (sentence s) of
                              Sort_gen_ax _ _ -> True
                              _               -> False) sens
        (eqPreds, realSens') = foldl findEqPredicates (Set.empty, []) realSens
        (genAxs,_) = partition isAxiom genSens
        insInjOps sig s =
              case sentence s of
              (Sort_gen_ax constrs _) ->
                 case recover_Sort_gen_ax constrs of
                 (_,ops,mp) -> assert (null mp) (insertInjOps sig ops)
              f -> assert (trace ("CASL.Inject.insertInjOps: Formula: \""
                                  ++showDoc f "\" slipped through filter.")
                                 True) sig
        filterPreds sig =
              sig { CSign.predMap = Map.difference
                (CSign.predMap sig)
                (Set.fold (\pl newMap -> case pl of
                      Pred_name pn -> insertPredToSet pn
                                           (Pred_type [] nullRange) newMap
                      Qual_pred_name pn pt _ -> insertPredToSet pn pt newMap)
                    Map.empty eqPreds) }
        insertPredToSet pId pType pMap =
              if (Map.member pId pMap)
                then Map.adjust insPredSet pId pMap
                else Map.insert pId (insPredSet Set.empty) pMap
            where
              insPredSet = Set.insert (CSign.toPredType pType)


{- |
 Finds definitions (Equivalences) where one side is a binary predicate
 and the other side is a built-in equality application (Strong_equation).
 The given Named (FORMULA f) is checked for this and if so, will be put
 into the set of such predicates.
-}
findEqPredicates :: (Show f, Eq f) => (Set.Set PRED_SYMB, [Named (FORMULA f)])
                    -- ^ previous list of found predicates and valid sentences
                 -> Named (FORMULA f)
                    -- ^ sentence to check
                 -> (Set.Set PRED_SYMB, [Named (FORMULA f)])
findEqPredicates (eqPreds, sens) sen =
    case (sentence sen) of
      Quantification Universal var_decl quantFormula _ ->
        isEquiv (foldl (\ vList (Var_decl v s _) ->
                          vList ++ map (\vl -> (vl, s)) v)
                       [] var_decl)
                quantFormula
      _ -> validSens

  where
    validSens = (eqPreds, sens ++ [sen])
    isEquiv vars qf =
      -- Exact two variables are checked if they have the same Sort.
      -- If more than two variables should be compared, use foldl.
      if (length vars == 2) && (snd (head vars) == snd (vars !! 1))
       then case qf of
          Equivalence f1 f2 _-> isStrong_eq vars f1 f2
          _                  -> validSens
        else validSens
    isStrong_eq vars f1 f2 =
      let f1n = case f1 of
                  Strong_equation _ _ _ -> f1
                  _                     -> f2
          f2n = case f1 of
                  Strong_equation _ _ _ -> f2
                  _                     -> f1
      in  case f1n of
            Strong_equation eq_t1 eq_t2 _ -> case f2n of
              Predication eq_pred_symb pterms _ ->
                if  (Map.toAscList (Map.fromList $ sortedVarTermList pterms)
                     == Map.toAscList (Map.fromList vars))
                 && (Map.toAscList
                         (Map.fromList $ sortedVarTermList [eq_t1, eq_t2])
                     == Map.toAscList (Map.fromList vars))
                  then (Set.insert eq_pred_symb eqPreds, sens)
                  else validSens
              _     -> validSens
            _       -> validSens

{- |
  Creates a list of (VAR, SORT) out of a list of TERMs. Only Qual_var TERMs
  are inserted which will be checked using
  'Comorphisms.CASL2SPASS.hasSortedVarTerm'.
-}
sortedVarTermList :: [TERM f]
                  -> [(VAR, SORT)]
sortedVarTermList ts = mapMaybe hasSortedVarTerm ts

{- |
  Finds a 'CASL.AS_Basic_CASL.Qual_var' term recursively if super term(s) is
  'CASL.AS_Basic_CASL.Sorted_term' or 'CASL.AS_Basic_CASL.Cast'.
-}
hasSortedVarTerm :: TERM f
                 -> Maybe (VAR, SORT)
hasSortedVarTerm t = case t of
    Qual_var v s _     -> Just (v,s)
    Sorted_term tx _ _ -> hasSortedVarTerm tx
    Cast tx _ _        -> hasSortedVarTerm tx
    _                  -> Nothing


------------------------------ Formulas ------------------------------

transOP_SYMB :: IdType_SPId_Map -> OP_SYMB -> SPIdentifier
transOP_SYMB idMap qo@(Qual_op_name op ot _) =
    maybe (error ("SuleCFOL2SoftFOL.transOP_SYMB: unknown op: " ++ show qo))
          id (lookupSPId op (COp (CSign.toOpType ot)) idMap)
transOP_SYMB _ (Op_name _) = error "SuleCFOL2SoftFOL: unqualified operation"

transPRED_SYMB :: IdType_SPId_Map -> PRED_SYMB -> SPIdentifier
transPRED_SYMB idMap qp@(Qual_pred_name p pt _) =
    maybe (error ("SuleCFOL2SoftFOL.transPRED_SYMB: unknown pred: " ++ show qp))
          id (lookupSPId p (CPred (CSign.toPredType pt)) idMap)
transPRED_SYMB _ (Pred_name _) = error "SuleCFOL2SoftFOL: unqualified predicate"

-- |
-- Translate the quantifier
quantify :: QUANTIFIER -> SPQuantSym
quantify q =
    case q of
    Universal -> SPForall
    Existential -> SPExists
    Unique_existential ->
        error "SuleCFOL2SoftFOL: no translation for existential quantification."

transVarTup :: (Set.Set SPIdentifier,IdType_SPId_Map) ->
               (VAR,SORT) ->
               ((Set.Set SPIdentifier,IdType_SPId_Map),
                (SPIdentifier,SPIdentifier))
                -- ^ ((new set of used Ids,new map of Ids to original Ids),
                --   (var as sp_Id,sort as sp_Id))
transVarTup (usedIds,idMap) (v,s) =
    ((Set.insert sid usedIds,
      insertSPId vi (CVar s) sid $ deleteSPId vi (CVar s) idMap)
    , (sid,spSort))
    where spSort = maybe (error ("SuleCFOL2SoftFOL: translation of sort \""++
                                showDoc s "\" not found"))
                         id (lookupSPId s CSort idMap)
          vi = simpleIdToId v
          sid = disSPOId (CVar s) (transId (CVar s) vi)
                    ["_Va_"++ showDoc s "_Va"]
                    usedIds

typedVarTerm :: SPIdentifier -> SPIdentifier -> SPTerm
typedVarTerm spVar spSort = compTerm (spSym spSort) [simpTerm (spSym spVar)]

spSym :: SPIdentifier -> SPSymbol
spSym = SPCustomSymbol

compTerm :: SPSymbol -> [SPTerm] -> SPTerm
compTerm = SPComplexTerm

simpTerm :: SPSymbol -> SPTerm
simpTerm = SPSimpleTerm

mkConj :: SPTerm -> SPTerm -> SPTerm
mkConj t1 t2 = compTerm SPAnd [t1,t2]

mkDisj :: SPTerm -> SPTerm -> SPTerm
mkDisj t1 t2 = compTerm SPOr [t1,t2]

mkEq :: SPTerm -> SPTerm -> SPTerm
mkEq t1 t2 = compTerm SPEqual [t1,t2]

mapSen :: (Eq f, Pretty f) => Bool
       -> FormulaTranslator f e
       -> CSign.Sign f e -> FORMULA f -> SPTerm
mapSen siSo trForm sign phi = transFORM siSo (Set.empty) sign
                                        (snd (transSign sign)) trForm phi

transFORM :: (Eq f, Pretty f) => Bool -- ^ single sorted flag
          -> Set.Set PRED_SYMB -- ^ list of predicates to substitute
          -> CSign.Sign f e
          -> IdType_SPId_Map -> FormulaTranslator f e
          -> FORMULA f -> SPTerm
transFORM siSo eqPreds sign i tr phi = transFORMULA siSo sign i tr phi'
    where phi' = codeOutConditionalF id
                     (codeOutUniqueExtF id id
                          (substEqPreds eqPreds id phi))


transFORMULA :: Pretty f => Bool -> CSign.Sign f e -> IdType_SPId_Map
             -> FormulaTranslator f e -> FORMULA f -> SPTerm
transFORMULA siSo sign idMap tr (Quantification qu vdecl phi _) =
    SPQuantTerm (quantify qu)
                    vList
                    (transFORMULA siSo sign idMap' tr phi)
    where ((_,idMap'),vList) =
              mapAccumL (\ acc e ->
                  let (acc',e') = transVarTup acc e
                  in (acc', (if siSo then simpTerm . spSym . fst
                                     else uncurry typedVarTerm)
                            e'))
                        (sidSet,idMap) (flatVAR_DECLs vdecl)
          sidSet = elemsSPId_Set idMap
transFORMULA siSo sign idMap tr (Conjunction phis _) =
  if null phis then SPSimpleTerm SPTrue
  else foldl1 mkConj (map (transFORMULA siSo sign idMap tr) phis)
transFORMULA siSo sign idMap tr (Disjunction phis _) =
  if null phis then SPSimpleTerm SPFalse
  else foldl1 mkDisj (map (transFORMULA siSo sign idMap tr) phis)
transFORMULA siSo sign idMap tr (Implication phi1 phi2 _ _) =
  compTerm SPImplies [transFORMULA siSo sign idMap tr phi1,
                           transFORMULA siSo sign idMap tr phi2]
transFORMULA siSo sign idMap tr (Equivalence phi1 phi2 _) =
  compTerm SPEquiv [transFORMULA siSo sign idMap tr phi1,
                    transFORMULA siSo sign idMap tr phi2]
transFORMULA siSo sign idMap tr (Negation phi _) =
  compTerm SPNot [transFORMULA siSo sign idMap tr phi]
transFORMULA _siSo _sign _idMap _tr (True_atom _)  = SPSimpleTerm SPTrue
transFORMULA _siSo _sign _idMap _tr (False_atom _) = SPSimpleTerm SPFalse
transFORMULA siSo sign idMap tr (Predication psymb args _) =
  compTerm (spSym (transPRED_SYMB idMap psymb))
           (map (transTERM siSo sign idMap tr) args)
transFORMULA siSo sign idMap tr (Existl_equation t1 t2 _)
    | term_sort t1 == term_sort t2 =
        mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
transFORMULA siSo sign idMap tr (Strong_equation t1 t2 _)
    | term_sort t1 == term_sort t2 =
        mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
transFORMULA _siSo sign idMap tr (ExtFORMULA phi) = tr sign idMap phi
transFORMULA _ _ _ _ (Definedness _ _) = SPSimpleTerm SPTrue -- totality assumed
transFORMULA siSo sign idMap tr (Membership t s _) =
  if siSo then SPSimpleTerm SPTrue
   else
    maybe (error ("SuleCFOL2SoftFOL.tF: no SoftFOL Id found for \""++
                  showDoc s "\""))
          (\si -> compTerm (spSym si) [transTERM siSo sign idMap tr t])
          (lookupSPId s CSort idMap)
transFORMULA _ _ _ _ (Sort_gen_ax _ _) =
    error "SuleCFOL2SoftFOL.transFORMULA: Sort generation constraints not\
          \ supported at this point!"
transFORMULA _ _ _ _ f =
    error ("SuleCFOL2SoftFOL.transFORMULA: unknown FORMULA '"++showDoc f "'")


transTERM :: Pretty f => Bool -> CSign.Sign f e -> IdType_SPId_Map
          -> FormulaTranslator f e -> TERM f -> SPTerm
transTERM _siSo _sign idMap _tr (Qual_var v s _) =
  maybe (error ("SuleCFOL2SoftFOL.tT: no SoftFOL Id found for \""++showDoc v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
transTERM siSo sign idMap tr (Application opsymb args _) =
    compTerm (spSym (transOP_SYMB idMap opsymb))
             (map (transTERM siSo sign idMap tr) args)

transTERM _siSo _sign _idMap _tr (Conditional _t1 _phi _t2 _) =
    error "SuleCFOL2SoftFOL.transTERM: Conditional terms must be coded out."

transTERM siSo sign idMap tr t'@(Sorted_term t s _)
    | term_sort t == s = recRes
    | otherwise =
        assert (trace ("Please check sorted term: '"++showDoc t' ""++
                       "' with sorts '"++show (term_sort t)++
                       "' <= '"++show s++"'")
                      (Set.member (term_sort t) (CSign.subsortsOf s sign)))
               recRes
    where recRes = transTERM siSo sign idMap tr t

transTERM siSo sign idMap tr t'@(Cast t s _)
    | term_sort t == s = recRes
    | otherwise =
          assert (trace ("Please check cast term: '"++showDoc t' ""++
                         "' with sorts '"++show s++
                         "' <= '"++show (term_sort t)++"'")
                        (Set.member s (CSign.subsortsOf (term_sort t) sign)))
                 recRes
    where recRes = transTERM siSo sign idMap tr t
transTERM _siSo _sign _idMap _tr t =
  error ("SuleCFOL2SoftFOL.transTERM: unknown TERM '"++showDoc t "'")

isSingleSorted :: CSign.Sign f e -> Bool
isSingleSorted sign = (Set.size (CSign.sortSet sign)) == 1

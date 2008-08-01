{- |
Module      :  $Header$
Description :  Coding of a CASL subset into SoftFOL
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from a CASL subset to SoftFOL.
-}

module Comorphisms.SuleCFOL2SoftFOL
    (SuleCFOL2SoftFOL(..), SuleCFOL2SoftFOLInduction(..))
    where

import Control.Exception

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils
import Common.Utils (mapAccumLM)
import qualified Common.Lib.Rel as Rel

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.List as List
import Data.Maybe
import Data.Char

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign as CSign
import CASL.Morphism
import CASL.Quantification
import CASL.Overload
import CASL.Utils
import CASL.Inject
import CASL.Induction (generateInductionLemmas)
import CASL.Simplify
-- SoftFOL
import SoftFOL.Sign as SPSign
import SoftFOL.Logic_SoftFOL
import SoftFOL.Translate
import SoftFOL.ParseTPTP

-- | The identity of the comorphisms
data SuleCFOL2SoftFOL = SuleCFOL2SoftFOL deriving (Show)
data SuleCFOL2SoftFOLInduction = SuleCFOL2SoftFOLInduction deriving (Show)

-- | SoftFOL theories
type SoftFOLTheory = (SPSign.Sign,[Named SPTerm])

data CType = CSort
           | CVar SORT
           | CPred CSign.PredType
           | COp   CSign.OpType
             deriving (Eq,Ord,Show)

toCKType :: CType -> CKType
toCKType ct = case ct of
  CSort -> CKSort
  CVar _ -> CKVar
  CPred _ -> CKPred
  COp _ -> CKOp

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
    assert (checkIdentifier (toCKType t) $ show spid) $
    Map.insertWith (Map.unionWith err) i (Map.insert t spid Map.empty) m
    where err = error ("SuleCFOL2SoftFOL: for Id \"" ++ show i ++
                       "\" the type \"" ++ show t ++
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
               CSign.Symbol RawSymbol Q_ProofTree
               SoftFOL () () SPTerm () ()
               SPSign.Sign
               SoftFOLMorphism SFSymbol () SPSign.ATP_ProofTree where
    sourceLogic SuleCFOL2SoftFOL = CASL
    sourceSublogic SuleCFOL2SoftFOL = SL.cFol
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature
                      , has_empty_sorts = True }
    targetLogic SuleCFOL2SoftFOL = SoftFOL
    mapSublogic SuleCFOL2SoftFOL sl =
        if isSubElem sl $ sourceSublogic SuleCFOL2SoftFOL
        then Just () else Nothing
    map_theory SuleCFOL2SoftFOL = transTheory sigTrCASL formTrCASL
    map_morphism = mapDefaultMorphism
    map_sentence SuleCFOL2SoftFOL sign =
      return . mapSen (isSingleSorted sign) formTrCASL sign
    extractModel SuleCFOL2SoftFOL = extractCASLModel
    has_model_expansion SuleCFOL2SoftFOL = True

instance Comorphism SuleCFOL2SoftFOLInduction
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol Q_ProofTree
               SoftFOL () () SPTerm () ()
               SPSign.Sign
               SoftFOLMorphism SFSymbol () SPSign.ATP_ProofTree where
    sourceLogic SuleCFOL2SoftFOLInduction = CASL
    sourceSublogic SuleCFOL2SoftFOLInduction = SL.cFol
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature }

    targetLogic SuleCFOL2SoftFOLInduction = SoftFOL
    mapSublogic SuleCFOL2SoftFOLInduction sl =
        if isSubElem sl $ sourceSublogic SuleCFOL2SoftFOLInduction
        then Just () else Nothing
    map_theory SuleCFOL2SoftFOLInduction =
        transTheory sigTrCASL formTrCASL . generateInductionLemmas
    map_morphism = mapDefaultMorphism
    map_sentence SuleCFOL2SoftFOLInduction sign =
      return . mapSen (isSingleSorted sign) formTrCASL sign
    extractModel SuleCFOL2SoftFOLInduction = extractCASLModel
    has_model_expansion SuleCFOL2SoftFOLInduction = True

---------------------------- Signature -----------------------------

transFuncMap :: IdType_SPId_Map ->
                CSign.Sign e f ->
                (FuncMap, IdType_SPId_Map)
transFuncMap idMap sign =
    Map.foldWithKey toSPOpType (Map.empty,idMap) (CSign.opMap sign)
    where toSPOpType iden typeSet (fm,im) =
              if Set.null typeSet then
                  error ("SuleCFOL2SoftFOL: empty sets are not " ++
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
                    sid fma t = disSPOId CKOp (transId CKOp iden)
                                       (uType (transOpType t))
                                       (Set.union (Map.keysSet fma)
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
                (PredMap, IdType_SPId_Map,[Named SPTerm])
transPredMap idMap sign =
    Map.foldWithKey toSPPredType (Map.empty,idMap,[]) (CSign.predMap sign)
    where toSPPredType iden typeSet (fm,im,sen) =
              if Set.null typeSet then
                  error ("SuleCFOL2SoftFOL: empty sets are not " ++
                         "allowed in PredMaps: " ++ show iden)
              else if Set.null $ Set.deleteMin typeSet then
                let pType = Set.findMin typeSet
                    sid' = sid fm pType
                in (Map.insert sid' (Set.singleton (transPredType pType)) fm
                   , insertSPId iden (CPred pType) sid' im
                   , sen)
              else case -- genPredImplicationDisjunctions sign $
                        partOverload (leqP sign)
                          (Set.singleton typeSet) of
                     (splitTySet) ->
                         let (fm',im') =
                                 Set.fold insOIdSet (fm,im) splitTySet
                         in (fm',im',sen)
              where insOIdSet tset (fm',im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transPredType tset) fm',
                            Set.fold (\ x y ->
                                          insertSPId iden (CPred x) sid' y)
                                     im' tset)
                    sid fma t = disSPOId CKPred (transId CKPred iden)
                                       (transPredType t)
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPId_Set idMap))

-- left typing implies right typing; explicit overloading sentences
-- are generated from these pairs, type TypePair = (CType,CType)

-- | disambiguation of SoftFOL Identifiers
disSPOId :: CKType -- ^ Type of CASl identifier
         -> SPIdentifier -- ^ translated CASL Identifier
         -> [SPIdentifier] -- ^ translated Sort Symbols of the profile
                           -- (maybe empty)
         -> Set.Set SPIdentifier -- ^ SoftFOL Identifiers already in use
         -> SPIdentifier -- ^ fresh Identifier generated from second argument;
    -- if the identifier was not in the set this is just the second argument
disSPOId cType sid ty idSet
    | checkIdentifier cType (show sid) && not (lkup $ show sid) = sid
    | otherwise = let nSid = disSPOId' $ show sid
                  in assert (checkIdentifier cType nSid) $ mkSimpleId nSid
    where disSPOId' sid'
              | not (lkup asid) = asid
              | otherwise = addType asid 1
              where asid = sid' ++ case cType of
                        CKSort -> ""
                        CKVar -> ""
                        x -> '_':show (length ty - (case x of
                                                    CKOp -> 1
                                                    _ -> 0))
                    addType res n =
                        let nres = asid ++ '_':fc n
                            nres' = nres ++ '_':show n
                        in if nres == res
                           then if nres' == res
                                then error ("SuleCFOL2SoftFOL: "
                                            ++ "cannot calculate"
                                            ++ " unambiguous id for "
                                            ++ show sid ++ " with type "
                                            ++ show ty
                                            ++ " and nres = " ++ nres
                                            ++ "\n with idSet "
                                            ++ show idSet)
                                else if not (lkup nres')
                                     then nres'
                                     else addType nres (n+1)
                           else if not (lkup nres)
                                then nres
                                else addType nres (n+1)
          lkup x = Set.member (mkSimpleId x) idSet
          fc n = concatMap (take n . show) ty

transOpType :: CSign.OpType -> ([SPIdentifier],SPIdentifier)
transOpType ot = (map transIdSort (CSign.opArgs ot),
                  transIdSort (CSign.opRes ot))

transPredType :: CSign.PredType -> [SPIdentifier]
transPredType pt = map transIdSort (CSign.predArgs pt)

-- | translate every Id as Sort
transIdSort :: Id -> SPIdentifier
transIdSort = transId CKSort

integrateGenerated :: (Pretty f, GetRange f) =>
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
                                                 , SPSign.predMap =
                                                     Map.union
                                                     (SPSign.predMap sign)
                                                               newPredsMap},
                                            mkInjSentences idMap' newOpsMap ++
                                            goalsAndSentences ++
                                            exhaustSens))))
                  mv

makeGenGoals :: (Pretty f, GetRange f) => IdType_SPId_Map -> [Named (FORMULA f)]
             -> (PredMap, IdType_SPId_Map, [Named SPTerm])
makeGenGoals idMap fs =
  let Result _ res = makeGens idMap fs
  in case res of
   Nothing -> (Map.empty, idMap, [])
   Just (_,_,idMap',fs') ->
     let fs'' = map (\s -> s {isAxiom = False}) fs'
     in (Map.empty,idMap',fs'')
 -- Sort_gen_ax as goals only implemented through a hack."
{- sketch of full implementation :
   - invent new predicate P that is supposed to hold on
     every x in the (freely) generated sort.
   - generate formulas with this predicate for each constructor.
   - recursive constructors hold if the predicate holds on the variables
   - prove forall x . P(x)

  implementation is postponed as this translation does not produce
only one goal, but additional symbols, axioms and a goal
 -}

makeGens :: (Pretty f, GetRange f) =>
            IdType_SPId_Map -> [Named (FORMULA f)]
         -> Result (SortMap, FuncMap, IdType_SPId_Map,[Named SPTerm])
            -- ^ The list of SoftFOL sentences gives exhaustiveness for
            -- generated sorts with only constant constructors
            -- and\/or subsort injections, by simply translating
            -- such sort generation constraints to disjunctions
makeGens idMap fs =
    case foldl makeGen (return (Map.empty,idMap,[],[])) fs of
    Result ds mv ->
        maybe (Result ds Nothing)
              (\ (opM,idMap',pairs,exhaustSens) ->
                   Result ds
                      (Just (foldr (uncurry Map.insert)
                                   Map.empty pairs,
                             opM,idMap',exhaustSens)))
              mv

makeGen :: (Pretty f, GetRange f) =>
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
                                            rList ++ genPairs,
                                            eSens ++ eSens')))
                 else mkError ("Non-injective sort mappings cannot " ++
                               "be translated to SoftFOL") (sentence nf)
      where -- compute standard form of sort generation constraints
            (srts,ops,mp) = recover_Sort_gen_ax constrs
            -- test whether a constructor belongs to a specific sort
            hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot
            hasTheSort _ _ = error "SuleCFOL2SoftFOL.hasTheSort"
            mkGen = Just . Generated free . map fst
            -- translate constraint for one sort
            makeGenP (opM,idMap,exSens) s = ((newOpMap, newIdMap,
                                                exSens ++ eSen ops_of_s s),
                                        (s', mkGen cons))
                where ((newOpMap,newIdMap),cons) =
                          mapAccumL mkInjOp (opM,idMap) ops_of_s
                      ops_of_s = List.filter (hasTheSort s) ops
                      s' = maybe (error $ "SuleCFOL2SoftFOL.makeGen: "
                                        ++ "No mapping found for '"
                                        ++ shows s "'") id
                                 (lookupSPId s CSort idMap)
            -- is an operation a constant or an injection ?
            -- (we currently can translate only these)
            isConstorInj o =
              nullArgs o ||
              take 7 (show (opSymbName o)) == "gn_inj_"
            -- generate sentences for one sort
            eSen os s = if all isConstorInj os
                        then [makeNamed (newName s) (SPQuantTerm SPForall
                                            [typedVarTerm var1 $
                                             maybe (error "lookup failed")
                                                   id
                                                   (lookupSPId s (CSort) iMap)]
                                            (disj var1 os))]
                        else []
            -- generate sentences: compute one disjunct (for one alternative)
            disjunct v o@(Qual_op_name _ (Op_type _ args _ _) _) =
              -- a constant? then just compare with it
              if nullArgs o then mkEq (varTerm v)
                                        (varTerm $ transOP_SYMB iMap o)
                -- an injection? then quantify existentially
                -- (for the injection's argument)
                else SPQuantTerm SPExists
                 [ typedVarTerm var2
                   $ maybe (error "lookup failed") id
                   $ lookupSPId (head args) (CSort) iMap ]
                 (mkEq (varTerm v)
                  (compTerm (SPCustomSymbol $ transOP_SYMB iMap o)
                   [varTerm var2]))
            disjunct _ _ = error "unqualified operation symbol"
            -- make disjunction out of all the alternatives
            disj v os = case map (disjunct v) os of
                        [] -> error "SuleCFOL2SoftFOL: no constructors found"
                        [x] -> x
                        xs -> foldl1 mkDisj xs
            -- generate enough variables
            var = fromJust (find (\ x ->
                      not (Set.member (mkSimpleId x) usedIds))
                            ("X":["X" ++ show i | i <- [(1::Int)..]]))
            var1 = mkSimpleId var
            var2 = mkSimpleId $ var ++ "a"
            varTerm v = simpTerm (spSym v)
            newName s = "ga_exhaustive_generated_sort_" ++ show (pretty s)
            usedIds = elemsSPId_Set iMap
            nullArgs o = case o of
                         Qual_op_name _ (Op_type _ args _ _) _ -> null args
                         _ -> error "SuleCFOL2SoftFOL: wrong constructor"
  _ -> r

mkInjOp :: (FuncMap, IdType_SPId_Map)
        -> OP_SYMB
        -> ((FuncMap,IdType_SPId_Map),
            (SPIdentifier,([SPIdentifier],SPIdentifier)))
mkInjOp (opM,idMap) qo@(Qual_op_name i ot _) =
    if isInjName i && isNothing lsid
       then ((Map.insert i' (Set.singleton (transOpType ot')) opM,
              insertSPId i (COp ot') i' idMap),
             (i', transOpType ot'))
       else ((opM,idMap),
             (maybe err id lsid,
              transOpType ot'))
    where i' = disSPOId CKOp (transId CKOp i)
                        (utype (transOpType ot')) usedNames
          ot' = CSign.toOpType ot
          lsid = lookupSPId i (COp ot') idMap
          usedNames = Map.keysSet opM
          err = error ("SuleCFOL2SoftFOL.mkInjOp: Cannot find SPId for '"
                       ++ show qo ++ "'")
          utype t = fst t ++ [snd t]
mkInjOp _ _ = error "SuleCFOL2SoftFOL.mkInjOp: Wrong constructor!!"

mkInjSentences :: IdType_SPId_Map
               -> FuncMap
               -> [Named SPTerm]
mkInjSentences idMap = Map.foldWithKey genInjs []
    where genInjs k tset fs = Set.fold (genInj k) fs tset
          genInj k (args,res) fs =
              assert (length args == 1)
                     $ makeNamed (newName (show k) (show $ head args)
                                 $ show res)
                       (SPQuantTerm SPForall
                              [typedVarTerm var $ head args]
                             (compTerm SPEqual
                                       [compTerm (spSym k)
                                                 [simpTerm (spSym var)],
                                        simpTerm (spSym var)])) : fs
          var = mkSimpleId $
            fromJust (find (\ x -> not (Set.member (mkSimpleId x) usedIds))
                          ("Y":["Y" ++ show i | i <- [(1::Int)..]]))
          newName o a r = "ga_" ++ o ++ '_' : a ++ '_' : r ++ "_id"
          usedIds = elemsSPId_Set idMap

{- |
  Translate a CASL signature into SoftFOL signature 'SoftFOL.Sign.Sign'.
  Before translating, eqPredicate symbols where removed from signature.
-}
transSign :: CSign.Sign f e ->
             (SPSign.Sign, IdType_SPId_Map, [Named SPTerm])
transSign sign = (SPSign.emptySign { SPSign.sortRel =
                                 Rel.map transIdSort (CSign.sortRel sign)
                           , sortMap = spSortMap
                           , funcMap = fMap
                           , SPSign.predMap = pMap
                           , singleSorted = isSingleSorted sign
                           }
                 , idMap''
                 , predImplications)
    where (spSortMap,idMap) =
            Set.fold (\ i (sm,im) ->
                          let sid = disSPOId CKSort (transIdSort i)
                                       [mkSimpleId $ take 20 (cycle "So")]
                                       (Map.keysSet sm)
                          in (Map.insert sid Nothing sm,
                              insertSPId i CSort sid im))
                                        (Map.empty,Map.empty)
                                        (CSign.sortSet sign)
          (fMap,idMap') =  transFuncMap idMap  sign
          (pMap,idMap'',predImplications) = transPredMap idMap' sign

nonEmptySortSens :: Set.Set SPIdentifier -> SortMap -> [Named SPTerm]
nonEmptySortSens emptySorts sm =
    Map.foldWithKey
      (\ s _ res ->
         if s `Set.member` emptySorts then res else extSen s : res)
      [] sm
    where extSen s = makeNamed ("ga_non_empty_sort_" ++ show s) $ SPQuantTerm
                     SPExists [varTerm] $ compTerm (spSym s) [varTerm]
              where varTerm = simpTerm $ spSym $ mkSimpleId $ newVar s
          newVar s = fromJust $ find (\ x -> x /= show s)
                          $ "Y" : ["Y" ++ show i | i <- [(1::Int)..]]

disjointTopSorts :: CSign.Sign f e -> IdType_SPId_Map -> [Named SPTerm]
disjointTopSorts sign idMap = let
    s = CSign.sortSet sign
    sl = Rel.partSet (have_common_supersorts True sign) s
    l = map (\ p -> case keepMinimals1 False sign id $ Set.toList p of
                       [e] -> e
                       _ -> error "disjointTopSorts") sl
    pairs ls = case ls of
      s1 : r -> map (\ s2 -> (s1, s2)) r ++ pairs r
      _ -> []
    v1 = simpTerm $ spSym $ mkSimpleId "Y1"
    v2 = simpTerm $ spSym $ mkSimpleId "Y2"
    in map (\ (t1, t2) ->
         makeNamed ("disjoint_sorts_" ++ shows t1 "_" ++ show t2) $
           SPQuantTerm SPForall
               [ compTerm (spSym t1) [v1]
               , compTerm (spSym t2) [v2]]
              $ compTerm SPNot [mkEq v1 v2]) $ pairs $
                map (\ t -> maybe (transIdSort t) id
                     $ lookupSPId t CSort idMap) l

transTheory :: (Pretty f, GetRange f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result SoftFOLTheory
transTheory trSig trForm (sign,sens) =
  fmap (trSig sign (CSign.extendedInfo sign))
    (case transSign (filterPreds $ foldl insInjOps sign genAxs) of
     (tSign,idMap,sign_sens) ->
        do (idMap',tSign',sentencesAndGoals) <-
               integrateGenerated idMap genSens tSign
           let tSignElim = if SPSign.singleSortNotGen tSign'
                             then tSign' {sortMap = Map.empty} else tSign'
               emptySorts = Set.map transIdSort (emptySortSet sign)
           return  (tSignElim,
                    sign_sens ++
                    disjointTopSorts sign idMap' ++
                    sentencesAndGoals ++
                    nonEmptySortSens emptySorts (sortMap tSignElim) ++
                    map (mapNamed (transFORM (singleSortNotGen tSign') eqPreds
                                     sign idMap' trForm))
                        realSens'))

  where (genSens,realSens) =
            partition (\ s -> case sentence s of
                              Sort_gen_ax _ _ -> True
                              _               -> False) sens
        (eqPreds, realSens') = foldl findEqPredicates (Set.empty, []) realSens
        (genAxs,_) = partition isAxiom genSens
        insInjOps sig s =
              case sentence s of
              (Sort_gen_ax constrs _) ->
                 case recover_Sort_gen_ax constrs of
                 (_,ops,mp) -> assert (null mp) (insertInjOps sig ops)
              _ -> error "SuleCFOL2SoftFOL.transTheory.insInjOps"
        filterPreds sig =
              sig { CSign.predMap = CSign.diffMapSet
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
                          vList ++ map (\ vl -> (vl, s)) v)
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
  'Comorphisms.SuleCFOL2SoftFOL.hasSortedVarTerm'.
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
transPRED_SYMB idMap qp@(Qual_pred_name p pt _) = maybe
    (error ("SuleCFOL2SoftFOL.transPRED_SYMB: unknown pred: " ++ show qp))
          id (lookupSPId p (CPred (CSign.toPredType pt)) idMap)
transPRED_SYMB _ (Pred_name _) =
    error "SuleCFOL2SoftFOL: unqualified predicate"

-- |
-- Translate the quantifier
quantify :: QUANTIFIER -> SPQuantSym
quantify q = case q of
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
    where spSort = maybe (error ("SuleCFOL2SoftFOL: translation of sort \"" ++
                                showDoc s "\" not found"))
                         id (lookupSPId s CSort idMap)
          vi = simpleIdToId v
          sid = disSPOId CKVar (transId CKVar vi)
                    [mkSimpleId $ "_Va_" ++ showDoc s "_Va"]
                    usedIds

mapSen :: (Eq f, Pretty f) => Bool
       -> FormulaTranslator f e
       -> CSign.Sign f e -> FORMULA f -> SPTerm
mapSen siSo trForm sign phi = transFORM siSo (Set.empty) sign
                                        ((\ (_,x,_) -> x) (transSign sign))
                                        trForm phi

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
  if null phis then simpTerm SPTrue
  else foldl1 mkConj (map (transFORMULA siSo sign idMap tr) phis)
transFORMULA siSo sign idMap tr (Disjunction phis _) =
  if null phis then simpTerm SPFalse
  else foldl1 mkDisj (map (transFORMULA siSo sign idMap tr) phis)
transFORMULA siSo sign idMap tr (Implication phi1 phi2 _ _) =
  compTerm SPImplies [transFORMULA siSo sign idMap tr phi1,
                           transFORMULA siSo sign idMap tr phi2]
transFORMULA siSo sign idMap tr (Equivalence phi1 phi2 _) =
  compTerm SPEquiv [transFORMULA siSo sign idMap tr phi1,
                    transFORMULA siSo sign idMap tr phi2]
transFORMULA siSo sign idMap tr (Negation phi _) =
  compTerm SPNot [transFORMULA siSo sign idMap tr phi]
transFORMULA _siSo _sign _idMap _tr (True_atom _)  = simpTerm SPTrue
transFORMULA _siSo _sign _idMap _tr (False_atom _) = simpTerm SPFalse
transFORMULA siSo sign idMap tr (Predication psymb args _) =
  compTerm (spSym (transPRED_SYMB idMap psymb))
           (map (transTERM siSo sign idMap tr) args)
transFORMULA siSo sign idMap tr (Existl_equation t1 t2 _)
    | sortOfTerm t1 == sortOfTerm t2 =
       mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
transFORMULA siSo sign idMap tr (Strong_equation t1 t2 _)
    | sortOfTerm t1 == sortOfTerm t2 =
       mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
transFORMULA _siSo sign idMap tr (ExtFORMULA phi) = tr sign idMap phi
transFORMULA _ _ _ _ (Definedness _ _) = simpTerm SPTrue -- assume totality
transFORMULA siSo sign idMap tr (Membership t s _) =
  if siSo then simpTerm SPTrue
   else
    maybe (error ("SuleCFOL2SoftFOL.tF: no SoftFOL Id found for \"" ++
                  showDoc s "\""))
          (\si -> compTerm (spSym si) [transTERM siSo sign idMap tr t])
          (lookupSPId s CSort idMap)
transFORMULA _ _ _ _ (Sort_gen_ax _ _) =
    error "SuleCFOL2SoftFOL.transFORMULA: Sort_gen_ax"
transFORMULA _ _ _ _ f =
    error ("SuleCFOL2SoftFOL.transFORMULA: unknown FORMULA '" ++ showDoc f "'")


transTERM :: Pretty f => Bool -> CSign.Sign f e -> IdType_SPId_Map
          -> FormulaTranslator f e -> TERM f -> SPTerm
transTERM _siSo _sign idMap _tr (Qual_var v s _) =
  maybe (error
         ("SuleCFOL2SoftFOL.tT: no SoftFOL Id found for \"" ++ showDoc v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
transTERM siSo sign idMap tr (Application opsymb args _) =
    compTerm (spSym (transOP_SYMB idMap opsymb))
             (map (transTERM siSo sign idMap tr) args)

transTERM _siSo _sign _idMap _tr (Conditional _t1 _phi _t2 _) =
    error "SuleCFOL2SoftFOL.transTERM: Conditional terms must be coded out."

transTERM siSo sign idMap tr (Sorted_term t s _)
    | sortOfTerm t == s = recRes
    | otherwise =
        assert (Set.member (sortOfTerm t) (CSign.subsortsOf s sign))
               recRes
    where recRes = transTERM siSo sign idMap tr t

transTERM siSo sign idMap tr (Cast t s _)
    | sortOfTerm t == s = recRes
    | otherwise =
          assert (Set.member s (CSign.subsortsOf (sortOfTerm t) sign))
                 recRes
    where recRes = transTERM siSo sign idMap tr t
transTERM _siSo _sign _idMap _tr t =
  error ("SuleCFOL2SoftFOL.transTERM: unknown TERM '" ++ showDoc t "'")

isSingleSorted :: CSign.Sign f e -> Bool
isSingleSorted sign =
  Set.size (CSign.sortSet sign) == 1
  && Set.null (emptySortSet sign) -- empty sorts need relativization

extractCASLModel :: CASLSign -> ATP_ProofTree
                 -> Result (CASLSign, [Named (FORMULA ())])
extractCASLModel sign (ATP_ProofTree output) =
  case parse tptpModel "" output of
    Right ts -> do
      let (_, idMap, _) = transSign sign
          rMap = getSignMap idMap
          allfs = map (\ (FormAnno _ (Name n) _ t _) -> (n, t)) ts
          rfs = filter ((/= "interpretation_domain") . fst) allfs
          (rs, ofs) = partition ((== "interpretation_atoms") . fst) rfs
      (nm, _) <- mapAccumLM (toForm sign) rMap $ map snd $ rs ++ ofs
      let nops = Map.filter (\ v -> case v of
            (COp ot, Nothing) | null (opArgs ot) -> True
            _ -> False) nm
          os = opMap sign
          nos = foldr (\ (i, (COp ot, _)) m ->
              addOpTo (simpleIdToId i) ot m) os
            $ Map.toList nops
          nsign = sign { opMap = nos }
      sens <- mapM (\ (n, f) -> do
         (_, cf) <- toForm nsign nm f
         return $ makeNamed n $ simplifyFormula id cf) rfs
      return (nsign, sens)
    Left err -> fail $ showErr err

type RMap = Map.Map SPIdentifier (CType, Maybe Id)

getSignMap :: IdType_SPId_Map -> RMap
getSignMap =
  foldr (\ (i, m) g -> foldr (\ (t, s) -> case t of
       CSort -> Map.insert s (CPred $ PredType [i], Nothing)
       _ -> Map.insert s (t, Just i)) g $ Map.toList m)
         Map.empty . Map.toList

toTERM :: Monad m => RMap -> SPTerm -> m (TERM ())
toTERM m spt = case spt of
  SPComplexTerm (SPCustomSymbol cst) args -> case Map.lookup cst m of
    Just (CVar s, _) | null args -> return $ Qual_var cst s nullRange
    Just (COp ot, Just i) | length args == length (opArgs ot) -> do
      ts <- mapM (toTERM m) args
      return $ Application  (Qual_op_name i (toOP_TYPE ot) nullRange)
        ts nullRange
    Just (COp ot, Nothing) | null args -> return $ Application
         (Qual_op_name (simpleIdToId cst) (toOP_TYPE ot) nullRange)
         [] nullRange
    _ -> fail "toTERM1"
  _ -> fail "toTERM2"

findTypes :: CASLSign -> SORT -> RMap -> SPTerm -> RMap
findTypes sign s m t = case t of
    SPComplexTerm (SPCustomSymbol cst) args ->
        case Map.lookup cst m of
          Nothing | null args -> if isVar cst
            then Map.insert cst (CVar s, Nothing) m
            else Map.insert cst (COp $ OpType Total [] s, Nothing) m
          Just (COp ot, _)
            | opRes ot == s && length args == length (opArgs ot) ->
                foldr (\ (n, a) m' -> findTypes sign n m' a) m
                   $ zip (opArgs ot) args
          Just (CVar s2, j) -> if s == s2 then m
              else case minimalSupers sign s s2 of
                [su] -> Map.insert cst (CVar su, j) m
                _ -> error ("inconsistent variable: " ++ show cst)
          _ -> error ("inconsistent symbol: " ++ show cst)
    _ -> error "findTypes"

toForm :: Monad m => CASLSign -> RMap -> SPTerm -> m (RMap, FORMULA ())
toForm sign m t = case t of
    SPQuantTerm q vars frm -> do
        let vs = concatMap getVars vars
            rm = foldr Map.delete m vs
        (nm, nf) <- toForm sign rm frm
        let m2 = foldr Map.delete nm vs
            nvs = catMaybes $ map (toVar nm) vars
        return $ (Map.union m m2, Quantification (toQuant q) nvs nf nullRange)
    SPComplexTerm SPEqual [a1, a2] -> do
        let nm = case (getType m a1, getType m a2) of
              (Nothing, Nothing) -> m
              (Just t1, Nothing) ->
                findTypes sign t1 (findTypes sign t1 m a1) a2
              (Nothing, Just t2) ->
                findTypes sign t2 (findTypes sign t2 m a1) a2
              (Just t1, Just t2) ->
                findTypes sign t2 (findTypes sign t1 m a1) a2
        let check = case (getType nm a1, getType nm a2) of
              (Just t1, Just t2) -> if t1 == t2 then True
                else have_common_supersorts True sign t1 t2
              _ -> True
        return $ case (toTERM nm a1, toTERM nm a2) of
            (Just t3, Just t4) | check ->
              (nm, Strong_equation t3 t4 nullRange)
            _ -> (nm, False_atom nullRange)
    SPComplexTerm (SPCustomSymbol cst) args ->
        case Map.lookup cst m of
          Just (CPred pt, mi) | length args == length (predArgs pt) -> do
              let nm = foldr (\ (s, a) m' -> findTypes sign s m' a) m
                       $ zip (predArgs pt) args
              ts <- mapM (toTERM nm) args
              return (nm, maybe (True_atom nullRange)
                 (\ i -> Predication
                (Qual_pred_name i (toPRED_TYPE pt) nullRange)
                ts nullRange) mi)
          _ -> fail $ "inconsistent pred symbol: " ++ show cst
    SPComplexTerm symb args -> do
         (nm, fs) <- mapAccumLM (toForm sign) m args
         case (symb, fs) of
           (SPNot, [f]) -> return (nm, Negation f nullRange)
           (SPImplies, [f1, f2]) ->
               return (nm, Implication f1 f2 True nullRange)
           (SPImplied, [f2, f1]) ->
               return (nm, Implication f1 f2 False nullRange)
           (SPEquiv, [f1, f2]) ->
               return (nm, Equivalence f1 f2 nullRange)
           (SPAnd, _) ->
               return (nm, Conjunction fs nullRange)
           (SPOr, _) ->
               return (nm, Disjunction fs nullRange)
           (SPTrue, []) -> return (nm, True_atom nullRange)
           (SPFalse, []) -> return (nm, False_atom nullRange)
           _ -> fail "toForm2"

toQuant :: SPQuantSym -> QUANTIFIER
toQuant sp = case sp of
  SPForall -> Universal
  SPExists -> Existential
  _ -> error "toQuant"

toVar :: Monad m => RMap -> SPTerm -> m VAR_DECL
toVar m sp = case sp of
  SPComplexTerm (SPCustomSymbol cst) [] | isVar cst -> case Map.lookup cst m of
    Just (CVar s, _) -> return $ Var_decl [cst] s nullRange
    _ -> fail $ "unknown variable: " ++ show cst
  _ -> fail $ "quantified term as variable: " ++ showDoc sp ""

getType :: RMap -> SPTerm -> Maybe SORT
getType m t = case t of
    SPComplexTerm (SPCustomSymbol cst) _ -> case Map.lookup cst m of
        Just (CVar s, _) -> Just s
        Just (COp ot, _) -> Just $ opRes ot
        _ -> Nothing
    _ -> Nothing

isVar :: SPIdentifier -> Bool
isVar cst = case tokStr cst of
    c : _ -> isUpper c
    "" -> error "isVar"

getVars :: SPTerm -> [SPIdentifier]
getVars tm = case tm of
    SPComplexTerm (SPCustomSymbol cst) args ->
        if null args then [cst] else concatMap getVars args
    _ -> []

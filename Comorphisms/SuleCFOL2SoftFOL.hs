{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/SuleCFOL2SoftFOL.hs
Description :  Coding of a CASL subset into SoftFOL
Copyright   :  (c) Klaus Luettich and Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from a CASL subset to SoftFOL.
-}

module Comorphisms.SuleCFOL2SoftFOL
  ( suleCFOL2SoftFOL
  , suleCFOL2SoftFOLInduction
  , suleCFOL2SoftFOLInduction2
  ) where

import Control.Exception (assert)
import Control.Monad (foldM)

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils
import Common.ProofTree
import Common.Utils
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.List as List
import Data.Maybe
import Data.Char
import Data.Function

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Cycle
import CASL.Sublogic as SL
import CASL.Sign as CSign
import CASL.MapSentence
import CASL.Morphism
import CASL.Quantification
import CASL.Overload
import CASL.Utils
import CASL.Inject
import CASL.Induction (generateInductionLemmas)
import CASL.Simplify
import CASL.ToDoc

import SoftFOL.Sign as SPSign
import SoftFOL.Logic_SoftFOL
import SoftFOL.Translate
import SoftFOL.ParseTPTP

data PlainSoftFOL = PlainSoftFOL

instance Show PlainSoftFOL where
  show PlainSoftFOL = "SoftFOL"

data SoftFOLInduction = SoftFOLInduction deriving Show
data SoftFOLInduction2 = SoftFOLInduction2 deriving Show

-- | The identity of the comorphisms
data GenSuleCFOL2SoftFOL a = GenSuleCFOL2SoftFOL a deriving Show

suleCFOL2SoftFOL :: GenSuleCFOL2SoftFOL PlainSoftFOL
suleCFOL2SoftFOL = GenSuleCFOL2SoftFOL PlainSoftFOL

suleCFOL2SoftFOLInduction :: GenSuleCFOL2SoftFOL SoftFOLInduction
suleCFOL2SoftFOLInduction = GenSuleCFOL2SoftFOL SoftFOLInduction

suleCFOL2SoftFOLInduction2 :: GenSuleCFOL2SoftFOL SoftFOLInduction2
suleCFOL2SoftFOLInduction2 = GenSuleCFOL2SoftFOL SoftFOLInduction2

-- | SoftFOL theories
type SoftFOLTheory = (SPSign.Sign, [Named SPTerm])

data CType = CSort
           | CVar SORT
           | CPred CSign.PredType
           | COp CSign.OpType
             deriving (Eq, Ord, Show)

toCKType :: CType -> CKType
toCKType ct = case ct of
  CSort -> CKSort
  CVar _ -> CKVar
  CPred _ -> CKPred
  COp _ -> CKOp

-- | CASL Ids with Types mapped to SPIdentifier
type IdTypeSPIdMap = Map.Map Id (Map.Map CType SPIdentifier)

-- | specialized lookup for IdTypeSPIdMap
lookupSPId :: Id -> CType -> IdTypeSPIdMap ->
          Maybe SPIdentifier
lookupSPId i t = maybe Nothing (Map.lookup t) . Map.lookup i

-- | specialized insert (with error) for IdTypeSPIdMap
insertSPId :: Id -> CType ->
              SPIdentifier ->
              IdTypeSPIdMap ->
              IdTypeSPIdMap
insertSPId i t spid m =
    assert (checkIdentifier (toCKType t) $ show spid) $
    Map.insertWith (Map.unionWith err) i (Map.insert t spid Map.empty) m
    where err = error ("SuleCFOL2SoftFOL: for Id \"" ++ show i ++
                       "\" the type \"" ++ show t ++
                       "\" can't be mapped to different SoftFOL identifiers")

deleteSPId :: Id -> CType ->
              IdTypeSPIdMap ->
              IdTypeSPIdMap
deleteSPId i t m =
    maybe m (\ m2 -> let m2' = Map.delete t m2
                     in if Map.null m2'
                           then Map.delete i m
                           else Map.insert i m2' m) $
          Map.lookup i m

-- | specialized elems into a set for IdTypeSPIdMap
elemsSPIdSet :: IdTypeSPIdMap -> Set.Set SPIdentifier
elemsSPIdSet = Map.fold (\ m res -> Set.union res
                                      (Set.fromList (Map.elems m)))
                         Set.empty

-- extended signature translation
type SignTranslator f e = CSign.Sign f e -> e -> SoftFOLTheory -> SoftFOLTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e =
    CSign.Sign f e -> IdTypeSPIdMap -> f -> SPTerm

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "SuleCFOL2SoftFOL: No extended formulas allowed in CASL"

instance Show a => Language (GenSuleCFOL2SoftFOL a) where
  language_name (GenSuleCFOL2SoftFOL a) = "CASL2" ++ show a

instance Show a => Comorphism (GenSuleCFOL2SoftFOL a)
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol ProofTree
               SoftFOL () [SPSign.TPTP] SPTerm () ()
               SPSign.Sign
               SoftFOLMorphism SFSymbol () ProofTree where
    sourceLogic (GenSuleCFOL2SoftFOL _) = CASL
    sourceSublogic (GenSuleCFOL2SoftFOL a) = SL.cFol
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature
                      , has_empty_sorts = show a == show PlainSoftFOL }
    sourceSublogicLossy (GenSuleCFOL2SoftFOL a) = SL.fol
                      { sub_features = LocFilSub
                      , has_empty_sorts = show a == show PlainSoftFOL }
    targetLogic (GenSuleCFOL2SoftFOL _) = SoftFOL
    mapSublogic cid sl =
        if isSubElem sl $ sourceSublogic cid
        then Just () else Nothing
    map_theory (GenSuleCFOL2SoftFOL a) = transTheory sigTrCASL formTrCASL
      . case show a of
      str | str == show SoftFOLInduction -> generateInductionLemmas True
          | str == show SoftFOLInduction2 -> generateInductionLemmas False
          | otherwise -> id
    extractModel (GenSuleCFOL2SoftFOL _) = extractCASLModel
    has_model_expansion (GenSuleCFOL2SoftFOL _) = True

-- -------------------------- Signature -----------------------------

transFuncMap :: IdTypeSPIdMap ->
                CSign.Sign e f ->
                (FuncMap, IdTypeSPIdMap)
transFuncMap idMap sign = Map.foldWithKey toSPOpType (Map.empty, idMap)
  . MapSet.toMap $ CSign.opMap sign
    where toSPOpType iden typeSet (fm, im) =
              if isSingleton typeSet then
                 let oType = Set.findMin typeSet
                     sid' = sid fm oType
                 in (Map.insert sid' (Set.singleton (transOpType oType)) fm,
                      insertSPId iden (COp oType) sid' im)
              else foldr insOIdSet (fm, im)
                $ Rel.partSet (leqF sign) typeSet
              where insOIdSet tset (fm', im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transOpType tset) fm',
                            Set.fold (\ x -> insertSPId iden (COp x) sid')
                                     im' tset)
                    sid fma t = disSPOId CKOp (transId CKOp iden)
                                       (uType (transOpType t))
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPIdSet idMap))
                    uType t = fst t ++ [snd t]

transPredMap :: IdTypeSPIdMap -> CSign.Sign e f
  -> (SPSign.PredMap, IdTypeSPIdMap)
transPredMap idMap sign =
    Map.foldWithKey toSPPredType (Map.empty, idMap) . MapSet.toMap
      $ CSign.predMap sign
    where toSPPredType iden typeSet (fm, im) =
              if isSingleton typeSet then
                let pType = Set.findMin typeSet
                    sid' = sid fm pType
                in (Map.insert sid' (Set.singleton (transPredType pType)) fm
                   , insertSPId iden (CPred pType) sid' im)
              else case -- genPredImplicationDisjunctions sign $
                        Rel.partSet (leqP sign) typeSet of
                     splitTySet -> foldr insOIdSet (fm, im) splitTySet
              where insOIdSet tset (fm', im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transPredType tset) fm',
                            Set.fold (\ x -> insertSPId iden (CPred x) sid')
                                     im' tset)
                    sid fma t = disSPOId CKPred (transId CKPred iden)
                                       (transPredType t)
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPIdSet idMap))

{- left typing implies right typing; explicit overloading sentences
are generated from these pairs, type TypePair = (CType,CType) -}

-- | disambiguation of SoftFOL Identifiers
disSPOId :: CKType -- ^ Type of CASl identifier
         -> SPIdentifier -- ^ translated CASL Identifier
         -> [SPIdentifier] {- ^ translated Sort Symbols of the profile
                           (maybe empty) -}
         -> Set.Set SPIdentifier -- ^ SoftFOL Identifiers already in use
         -> SPIdentifier {- ^ fresh Identifier generated from second argument;
    if the identifier was not in the set this is just the second argument -}
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
                        x -> '_' : show (length ty - (case x of
                                                    CKOp -> 1
                                                    _ -> 0))
                    addType res n =
                        let nres = asid ++ '_' : fc n
                            nres' = nres ++ '_' : show n
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
                                     else addType nres (n + 1)
                           else if not (lkup nres)
                                then nres
                                else addType nres (n + 1)
          lkup x = Set.member (mkSimpleId x) idSet
          fc n = concatMap (take n . show) ty

transOpType :: CSign.OpType -> ([SPIdentifier], SPIdentifier)
transOpType ot = (map transIdSort (CSign.opArgs ot),
                  transIdSort (CSign.opRes ot))

transPredType :: CSign.PredType -> [SPIdentifier]
transPredType = map transIdSort . CSign.predArgs

-- | translate every Id as Sort
transIdSort :: Id -> SPIdentifier
transIdSort = transId CKSort

integrateGenerated :: IdTypeSPIdMap -> [Named (FORMULA f)] ->
                      SPSign.Sign ->
                      Result (IdTypeSPIdMap, SPSign.Sign, [Named SPTerm])
integrateGenerated idMap genSens sign
    | null genSens = return (idMap, sign, [])
    | otherwise =
      case partition isAxiom genSens of
      (genAxs, genGoals) ->
        case makeGenGoals sign idMap genGoals of
        (newPredsMap, idMap', goalsAndSentences) ->
          -- makeGens must not invent new sorts
          case makeGens sign idMap' genAxs of
          Result dias mv ->
            maybe (Result dias Nothing)
                  (\ (spSortMap_makeGens, newOpsMap, idMap'', exhaustSens) ->
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

makeGenGoals :: SPSign.Sign -> IdTypeSPIdMap -> [Named (FORMULA f)]
             -> (SPSign.PredMap, IdTypeSPIdMap, [Named SPTerm])
makeGenGoals sign idMap fs =
  let Result _ res = makeGens sign idMap fs
  in case res of
   Nothing -> (Map.empty, idMap, [])
   Just (_, _, idMap', fs') ->
     let fs'' = map (\ s -> s {isAxiom = False}) fs'
     in (Map.empty, idMap', fs'')
 {- Sort_gen_ax as goals only implemented through a hack."
sketch of full implementation :
   - invent new predicate P that is supposed to hold on
     every x in the (freely) generated sort.
   - generate formulas with this predicate for each constructor.
   - recursive constructors hold if the predicate holds on the variables
   - prove forall x . P(x)

  implementation is postponed as this translation does not produce
only one goal, but additional symbols, axioms and a goal
 -}

makeGens :: SPSign.Sign -> IdTypeSPIdMap -> [Named (FORMULA f)]
         -> Result (SortMap, FuncMap, IdTypeSPIdMap, [Named SPTerm])
            {- ^ The list of SoftFOL sentences gives exhaustiveness for
            generated sorts with only constant constructors
            and\/or subsort injections, by simply translating
            such sort generation constraints to disjunctions -}
makeGens sign idMap fs =
    case foldl (makeGen sign) (return (Map.empty, idMap, [], [])) fs of
    Result ds mv ->
        maybe (Result ds Nothing)
              (\ (opM, idMap', pairs, exhaustSens) ->
                   Result ds
                      (Just (foldr (uncurry Map.insert)
                                   Map.empty pairs,
                             opM, idMap', exhaustSens)))
              mv

makeGen :: SPSign.Sign
        -> Result (FuncMap, IdTypeSPIdMap,
                   [(SPIdentifier, Maybe Generated)], [Named SPTerm])
        -> Named (FORMULA f)
        -> Result (FuncMap, IdTypeSPIdMap,
                   [(SPIdentifier, Maybe Generated)], [Named SPTerm])
makeGen sign r@(Result ods omv) nf =
    maybe (Result ods Nothing) process omv where
 process (oMap, iMap, rList, eSens) = case sentence nf of
  Sort_gen_ax constrs free ->
      if null mp then (case mapAccumL makeGenP (oMap, iMap, []) srts of
                       ((oMap', iMap', eSens'), genPairs) ->
                          Result ods (Just (oMap', iMap',
                                            rList ++ genPairs,
                                            eSens ++ eSens')))
                 else mkError ("Sort generation constraints with " ++
                               "non-injective sort mappings cannot " ++
                               "be translated to SoftFOL") mp
      where -- compute standard form of sort generation constraints
            (srts, ops, mp) = recover_Sort_gen_ax constrs
            -- test whether a constructor belongs to a specific sort
            hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot
            hasTheSort _ _ = error "SuleCFOL2SoftFOL.hasTheSort"
            mkGen = Just . Generated free . map fst
            -- translate constraint for one sort
            makeGenP (opM, idMap, exSens) s = ((newOpMap, newIdMap,
                                                exSens ++ eSen ops_of_s s),
                                        (s', mkGen cons))
                where ((newOpMap, newIdMap), cons) =
                          mapAccumL mkInjOp (opM, idMap) ops_of_s
                      ops_of_s = List.filter (hasTheSort s) ops
                      s' = fromMaybe (error $ "SuleCFOL2SoftFOL.makeGen: "
                                        ++ "No mapping found for '"
                                        ++ shows s "'")
                                 (lookupSPId s CSort idMap)
            {- is an operation a constant or an injection ?
            (we currently can translate only these) -}
            isConstorInj o =
              nullArgs o || isInjName (opSymbName o)
            -- generate sentences for one sort
            eSen os s = [ makeNamed (newName s) (SPQuantTerm SPForall
                            [typedVarTerm var1
                             $ fromMaybe (error "lookup failed")
                             (lookupSPId s CSort iMap)] (disj var1 os))
                        | all isConstorInj os ]
            -- generate sentences: compute one disjunct (for one alternative)
            mkDisjunct v o@(Qual_op_name _ (Op_type _ args res _) _) =
              -- a constant? then just compare with it
              case args of
                [] -> mkEq (varTerm v) $ varTerm $ transOPSYMB iMap o
                {- an injection? then quantify existentially
                (for the injection's argument)
                since injections are identities, we can leave them out -}
                [arg] -> let ta = transIdSort arg in SPQuantTerm SPExists
                  [ typedVarTerm var2 ta ]
                   $ mkEq (varTerm v)
                   $ if Rel.member ta (transIdSort res)
                        $ SPSign.sortRel sign
                     then varTerm var2
                     else compTerm (spSym $ transOPSYMB iMap o) [varTerm var2]
                _ -> error "cannot handle ordinary constructors"
            mkDisjunct _ _ = error "unqualified operation symbol"
            -- make disjunction out of all the alternatives
            disj v os = case map (mkDisjunct v) os of
                        [] -> error "SuleCFOL2SoftFOL: no constructors found"
                        [x] -> x
                        xs -> foldl1 mkDisj xs
            -- generate enough variables
            var = fromJust (find (\ x ->
                      not (Set.member (mkSimpleId x) usedIds))
                            ("X" : ['X' : show i | i <- [(1 :: Int) ..]]))
            var1 = mkSimpleId var
            var2 = mkSimpleId $ var ++ "a"
            varTerm = simpTerm . spSym
            newName s = "ga_exhaustive_generated_sort_" ++ show (pretty s)
            usedIds = elemsSPIdSet iMap
            nullArgs o = case o of
                         Qual_op_name _ (Op_type _ args _ _) _ -> null args
                         _ -> error "SuleCFOL2SoftFOL: wrong constructor"
  _ -> r

mkInjOp :: (FuncMap, IdTypeSPIdMap)
        -> OP_SYMB
        -> ((FuncMap, IdTypeSPIdMap),
            (SPIdentifier, ([SPIdentifier], SPIdentifier)))
mkInjOp (opM, idMap) qo@(Qual_op_name i ot _) =
    if isInjName i && isNothing lsid
       then ((Map.insert i' (Set.singleton (transOpType ot')) opM,
              insertSPId i (COp ot') i' idMap),
             (i', transOpType ot'))
       else ((opM, idMap),
             (fromMaybe err lsid,
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

mkInjSentences :: IdTypeSPIdMap
               -> FuncMap
               -> [Named SPTerm]
mkInjSentences idMap = Map.foldWithKey genInjs []
    where genInjs k tset fs = Set.fold (genInj k) fs tset
          genInj k (args, res) =
              assert (length args == 1)
                     . (makeNamed (newName (show k) (show $ head args)
                                 $ show res)
                       (SPQuantTerm SPForall
                              [typedVarTerm var $ head args]
                             (compTerm SPEqual
                                       [compTerm (spSym k)
                                                 [simpTerm (spSym var)],
                                        simpTerm (spSym var)])) :)
          var = mkSimpleId $
            fromJust (find (\ x -> not (Set.member (mkSimpleId x) usedIds))
                          ("Y" : [ 'Y' : show i | i <- [(1 :: Int) ..]]))
          newName o a r = "ga_" ++ o ++ '_' : a ++ '_' : r ++ "_id"
          usedIds = elemsSPIdSet idMap

{- |
  Translate a CASL signature into SoftFOL signature 'SoftFOL.Sign.Sign'.
  Before translating, eqPredicate symbols where removed from signature.
-}
transSign :: CSign.Sign f e -> (SPSign.Sign, IdTypeSPIdMap)
transSign sign = (SPSign.emptySign { SPSign.sortRel =
                                 Rel.map transIdSort (CSign.sortRel sign)
                           , sortMap = spSortMap
                           , funcMap = fMap
                           , SPSign.predMap = pMap
                           , singleSorted = isSingleSorted sign
                           }
                 , idMap'')
    where (spSortMap, idMap) =
            Set.fold (\ i (sm, im) ->
                          let sid = disSPOId CKSort (transIdSort i)
                                       [mkSimpleId $ take 20 (cycle "So")]
                                       (Map.keysSet sm)
                          in (Map.insert sid Nothing sm,
                              insertSPId i CSort sid im))
                                        (Map.empty, Map.empty)
                                        (CSign.sortSet sign)
          (fMap, idMap') = transFuncMap idMap sign
          (pMap, idMap'') = transPredMap idMap' sign

nonEmptySortSens :: CSign.Sign f e -> IdTypeSPIdMap -> SortMap -> [Named SPTerm]
nonEmptySortSens sig idMap sm =
  let es = Set.difference (sortSet sig) $ emptySortSet sig
  in [ extSen s | nes <- Set.toList es
     , let s = fromMaybe (transIdSort nes) $ lookupSPId nes CSort idMap
     , Set.member s $ Map.keysSet sm ]
    where extSen s = makeNamed ("ga_non_empty_sort_" ++ show s) $ SPQuantTerm
                     SPExists [varTerm] $ compTerm (spSym s) [varTerm]
              where varTerm = simpTerm $ spSym $ mkSimpleId $ newVar s
          newVar s = fromJust $ find (/= show s)
                          $ "Y" : ['Y' : show i | i <- [(1 :: Int) ..]]

disjointTopSorts :: CSign.Sign f e -> IdTypeSPIdMap -> [Named SPTerm]
disjointTopSorts sign idMap = let
    s = CSign.sortSet sign
    sl = Rel.partSet (haveCommonSupersorts True sign) s
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
                map (\ t -> fromMaybe (transIdSort t)
                     $ lookupSPId t CSort idMap) l

transTheory :: (FormExtension f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result SoftFOLTheory
transTheory trSig trForm (sign, sens) =
  let (nsig, sm) = removeSortCycles sign
  in transTheoryAux trSig trForm (nsig
     , map (mapNamed $ mapMorphForm (return id)
                 ((embedMorphism () sign nsig) { sort_map = sm })) sens)

transTheoryAux :: (FormExtension f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result SoftFOLTheory
transTheoryAux trSig trForm (sign, sens) =
  fmap (trSig sign (CSign.extendedInfo sign))
    (case transSign (filterPreds $ foldl insInjOps sign genAxs) of
     (tSign, idMap) ->
        do (idMap', tSign', sentencesAndGoals) <-
               integrateGenerated idMap genSens tSign
           let tSignElim = if SPSign.singleSortNotGen tSign'
                             then tSign' {sortMap = Map.empty} else tSign'
           return (tSignElim,
                    disjointTopSorts sign idMap' ++
                    sentencesAndGoals ++
                    nonEmptySortSens sign idMap' (sortMap tSignElim) ++
                    map (mapNamed (transFORM (singleSortNotGen tSign') eqPreds
                                     sign idMap' trForm))
                        realSens'))

  where (genSens, realSens) =
            partition (\ s -> case sentence s of
                              Sort_gen_ax _ _ -> True
                              _ -> False) sens
        (eqPreds, realSens') = foldl findEqPredicates (Set.empty, []) realSens
        genAxs = filter isAxiom genSens
        insInjOps sig s =
              case sentence s of
              (Sort_gen_ax constrs _) ->
                 case recover_Sort_gen_ax constrs of
                 (_, ops, mp) -> assert (null mp) (insertInjOps sig ops)
              _ -> error "SuleCFOL2SoftFOL.transTheory.insInjOps"
        filterPreds sig =
              sig { CSign.predMap = MapSet.difference
                (CSign.predMap sig)
                (Set.fold (\ pl -> case pl of
                      Pred_name pn -> MapSet.insert pn (PredType [])
                      Qual_pred_name pn pt _ ->
                        MapSet.insert pn $ CSign.toPredType pt)
                    MapSet.empty eqPreds) }

{- |
 Finds definitions (Equivalences) where one side is a binary predicate
 and the other side is a built-in equality application (Strong_equation).
 The given Named (FORMULA f) is checked for this and if so, will be put
 into the set of such predicates.
-}
findEqPredicates :: (Eq f) => (Set.Set PRED_SYMB, [Named (FORMULA f)])
                    -- ^ previous list of found predicates and valid sentences
                 -> Named (FORMULA f)
                    -- ^ sentence to check
                 -> (Set.Set PRED_SYMB, [Named (FORMULA f)])
findEqPredicates (eqPreds, sens) sen =
    case sentence sen of
      Quantification Universal var_decl quantFormula _ ->
        isEquiv (foldl (\ vList (Var_decl v s _) ->
                          vList ++ map (\ vl -> (vl, s)) v)
                       [] var_decl)
                quantFormula
      _ -> validSens

  where
    validSens = (eqPreds, sens ++ [sen])
    isEquiv vars qf =
      {- Exact two variables are checked if they have the same Sort.
      If more than two variables should be compared, use foldl. -}
      if (length vars == 2) && (snd (head vars) == snd (vars !! 1))
       then case qf of
          Relation f1 Equivalence f2 _ -> isStrong_eq vars f1 f2
          _ -> validSens
        else validSens
    isStrong_eq vars f1 f2 =
      let f1n = case f1 of
                  Equation _ Strong _ _ -> f1
                  _ -> f2
          f2n = case f1 of
                  Equation _ Strong _ _ -> f2
                  _ -> f1
      in case f1n of
            Equation eq_t1 Strong eq_t2 _ -> case f2n of
              Predication eq_pred_symb pterms _ ->
                if Map.toList (Map.fromList $ sortedVarTermList pterms)
                     == Map.toList (Map.fromList vars)
                 && Map.toList
                         (Map.fromList $ sortedVarTermList [eq_t1, eq_t2])
                     == Map.toList (Map.fromList vars)
                  then (Set.insert eq_pred_symb eqPreds, sens)
                  else validSens
              _ -> validSens
            _ -> validSens

{- |
  Creates a list of (VAR, SORT) out of a list of TERMs. Only Qual_var TERMs
  are inserted which will be checked using
  'Comorphisms.SuleCFOL2SoftFOL.hasSortedVarTerm'.
-}
sortedVarTermList :: [TERM f] -> [(VAR, SORT)]
sortedVarTermList = mapMaybe hasSortedVarTerm

{- |
  Finds a 'CASL.AS_Basic_CASL.Qual_var' term recursively if super term(s) is
  'CASL.AS_Basic_CASL.Sorted_term' or 'CASL.AS_Basic_CASL.Cast'.
-}
hasSortedVarTerm :: TERM f -> Maybe (VAR, SORT)
hasSortedVarTerm t = case t of
    Qual_var v s _ -> Just (v, s)
    Sorted_term tx _ _ -> hasSortedVarTerm tx
    Cast tx _ _ -> hasSortedVarTerm tx
    _ -> Nothing


-- ---------------------------- Formulas ------------------------------

transOPSYMB :: IdTypeSPIdMap -> OP_SYMB -> SPIdentifier
transOPSYMB idMap ~qo@(Qual_op_name op ot _) =
    fromMaybe (error $ "SuleCFOL2SoftFOL.transOPSYMB: unknown op: " ++ show qo)
        (lookupSPId op (COp (CSign.toOpType ot)) idMap)

transPREDSYMB :: IdTypeSPIdMap -> PRED_SYMB -> SPIdentifier
transPREDSYMB idMap ~qp@(Qual_pred_name p pt _) = fromMaybe
    (error $ "SuleCFOL2SoftFOL.transPREDSYMB: unknown pred: " ++ show qp)
          (lookupSPId p (CPred (CSign.toPredType pt)) idMap)

-- | Translate the quantifier
quantify :: QUANTIFIER -> SPQuantSym
quantify q = case q of
    Universal -> SPForall
    Existential -> SPExists
    Unique_existential ->
      error "SuleCFOL2SoftFOL: no translation for existential quantification."

transVarTup :: (Set.Set SPIdentifier, IdTypeSPIdMap) ->
               (VAR, SORT) ->
               ((Set.Set SPIdentifier, IdTypeSPIdMap),
                (SPIdentifier, SPIdentifier))
                {- ^ ((new set of used Ids, new map of Ids to original Ids),
                (var as sp_Id, sort as sp_Id)) -}
transVarTup (usedIds, idMap) (v, s) =
    ((Set.insert sid usedIds,
      insertSPId vi (CVar s) sid $ deleteSPId vi (CVar s) idMap)
    , (sid, spSort))
    where spSort = fromMaybe
            (error $ "SuleCFOL2SoftFOL: translation of sort \"" ++
             showDoc s "\" not found")
            (lookupSPId s CSort idMap)
          vi = simpleIdToId v
          sid = disSPOId CKVar (transId CKVar vi)
                    [mkSimpleId $ "_Va_" ++ showDoc s "_Va"]
                    usedIds

transFORM :: (Eq f, FormExtension f) => Bool -- ^ single sorted flag
          -> Set.Set PRED_SYMB -- ^ list of predicates to substitute
          -> CSign.Sign f e
          -> IdTypeSPIdMap -> FormulaTranslator f e
          -> FORMULA f -> SPTerm
transFORM siSo eqPreds sign i tr phi = transFORMULA siSo sign i tr phi'
    where phi' = codeOutConditionalF id
                     (codeOutUniqueExtF id id
                          (substEqPreds eqPreds id phi))


transFORMULA :: FormExtension f => Bool -> CSign.Sign f e -> IdTypeSPIdMap
             -> FormulaTranslator f e -> FORMULA f -> SPTerm
transFORMULA siSo sign idMap tr frm = case frm of
  Quantification qu vdecl phi _ ->
    SPQuantTerm (quantify qu)
                    vList
                    (transFORMULA siSo sign idMap' tr phi)
    where ((_, idMap'), vList) =
              mapAccumL (\ acc e ->
                  let (acc', e') = transVarTup acc e
                  in (acc', (if siSo then simpTerm . spSym . fst
                                     else uncurry typedVarTerm)
                            e'))
                        (sidSet, idMap) (flatVAR_DECLs vdecl)
          sidSet = elemsSPIdSet idMap
  Junction j phis _ -> let
    (n, op) = if j == Dis then (SPFalse, mkDisj) else (SPTrue, mkConj)
    in if null phis then simpTerm n else
    foldl1 op (map (transFORMULA siSo sign idMap tr) phis)
  Relation phi1 c phi2 _ -> compTerm
    (if c == Equivalence then SPEquiv else SPImplies)
    [transFORMULA siSo sign idMap tr phi1, transFORMULA siSo sign idMap tr phi2]
  Negation phi _ -> compTerm SPNot [transFORMULA siSo sign idMap tr phi]
  Atom b _ -> simpTerm $ if b then SPTrue else SPFalse
  Predication psymb args _ -> compTerm (spSym (transPREDSYMB idMap psymb))
           (map (transTERM siSo sign idMap tr) args)
  Equation t1 _ t2 _ -> -- sortOfTerm t1 == sortOfTerm t2
       mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
  ExtFORMULA phi -> tr sign idMap phi
  Definedness _ _ -> simpTerm SPTrue -- assume totality
  Membership t s _ -> if siSo then simpTerm SPTrue else
    maybe (error ("SuleCFOL2SoftFOL.tF: no SoftFOL Id found for \"" ++
                  showDoc s "\""))
          (\ si -> compTerm (spSym si) [transTERM siSo sign idMap tr t])
          (lookupSPId s CSort idMap)
  _ -> error
    $ "SuleCFOL2SoftFOL.transFORMULA: unknown FORMULA '" ++ showDoc frm "'"

transTERM :: FormExtension f => Bool -> CSign.Sign f e -> IdTypeSPIdMap
          -> FormulaTranslator f e -> TERM f -> SPTerm
transTERM siSo sign idMap tr term = case term of
  Qual_var v s _ -> maybe
    (error
         ("SuleCFOL2SoftFOL.tT: no SoftFOL Id found for \"" ++ showDoc v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
  Application opsymb args _ ->
    compTerm (spSym (transOPSYMB idMap opsymb))
             (map (transTERM siSo sign idMap tr) args)
  Conditional _t1 _phi _t2 _ ->
    error "SuleCFOL2SoftFOL.transTERM: Conditional terms must be coded out."
  Sorted_term t _s _ -> -- sortOfTerm t isSubsortOf s
    transTERM siSo sign idMap tr t
  Cast t _s _ -> -- s isSubsortOf sortOfTerm t
    transTERM siSo sign idMap tr t
  _ -> error ("SuleCFOL2SoftFOL.transTERM: unknown TERM '" ++ showDoc term "'")

isSingleSorted :: CSign.Sign f e -> Bool
isSingleSorted sign =
  Set.size (CSign.sortSet sign) == 1
  && Set.null (emptySortSet sign) -- empty sorts need relativization

-- * extract model out of darwin output stored in a proof tree

extractCASLModel :: CASLSign -> ProofTree
  -> Result (CASLSign, [Named (FORMULA ())])
extractCASLModel sign (ProofTree output) =
  case parse tptpModel "" output of
    Right rfs -> do
      let idMap = snd $ transSign sign
          rMap = getSignMap idMap
          (rs, fs1) = partition ((== "interpretation_atoms") . fst) rfs
          (ds, fs2) = partition ((== "interpretation_domain") . fst) fs1
          (dds, fs3) = partition
            ((== "interpretation_domain_distinct") . fst) fs2
          (es, nm0) = foldl (\ (l, m) (_, s) -> let
                           (e, m2) = typeCheckForm False sign m s
                           in (l ++ e, m2)) ([], rMap) rs
          nm = foldl (\ m (_, s) -> snd $ typeCheckForm True sign m s) nm0
               $ fs3 ++ ds ++ dds
          nops = Map.filter (\ v -> case v of
            (COp _, Nothing) -> True
            _ -> False) nm
          os = opMap sign
          nos = foldr (\ (i, ~(COp ot, _)) -> addOpTo (simpleIdToId i) ot) os
            $ Map.toList nops
          nsign = sign { opMap = nos }
          mkWarn s = Diag Warning s nullRange
      doms <- if Set.null (sortSet sign) then return [] else
        mapM (\ (n, f) -> do
          diss <- getDomElems f
          nf <- createDomain sign nm diss
          return $ makeNamed n nf) ds
      distfs <- mapM (\ (n, f) -> do
          let fs = splitConjs f
              ets = map (fst . typeCheckForm False sign nm) fs
              cs = filter (null . fst) $ zip ets fs
          dts <- foldM getUneqElems Set.empty fs
          let ws = concatMap ((\ (s, _, _) -> s)
                              . typeCheckTerm sign Nothing nm)
                   $ Set.toList dts
          Result (map mkWarn ws) $ Just ()
          tfs <- mapM (toForm nsign nm . snd) cs
          return $ makeNamed n $ simplifyFormula id $ conjunct tfs) dds
      terms <- mapM (\ (n, f) -> do
          let fs = splitConjs f
              ets = map (fst . typeCheckForm False sign nm) fs
              (cs, ws) = partition (null . fst) $ zip ets fs
          Result (map mkWarn $ concatMap fst ws) $ Just ()
          tfs <- mapM (toForm nsign nm . snd) cs
          return $ makeNamed n $ simplifyFormula id $ conjunct tfs) fs3
      sens <- mapM (\ (n, f) -> do
         cf <- toForm nsign nm f
         return $ makeNamed n $ simplifyFormula id cf) rs
      Result (map mkWarn es) $ Just ()
      return (nsign, doms ++ distfs ++ terms ++ sens)
    Left err -> fail $ showErr err

type RMap = Map.Map SPIdentifier (CType, Maybe Id)

getSignMap :: IdTypeSPIdMap -> RMap
getSignMap =
  foldr (\ (i, m) g -> foldr (\ (t, s) -> case t of
       CSort -> Map.insert s (CPred $ PredType [i], Nothing)
       _ -> Map.insert s (t, Just i)) g $ Map.toList m)
         Map.empty . Map.toList

splitConjs :: SPTerm -> [SPTerm]
splitConjs trm = case trm of
  SPComplexTerm SPAnd args ->
     concatMap splitConjs args
  _ -> [trm]

getUneqElems :: Set.Set SPTerm -> SPTerm -> Result (Set.Set SPTerm)
getUneqElems s trm = case trm of
  SPComplexTerm SPNot [SPComplexTerm SPEqual [a1, a2]] ->
      return $ Set.insert a2 $ Set.insert a1 s
  _ -> fail $ "unexpected disjointness formula: " ++ showDoc trm ""

splitDisjs :: SPTerm -> [SPTerm]
splitDisjs trm = case trm of
  SPComplexTerm SPOr args ->
     concatMap splitDisjs args
  _ -> [trm]

getDomElems :: SPTerm -> Result [SPTerm]
getDomElems trm = case trm of
  SPQuantTerm SPForall [var] frm ->
      mapM (\ t -> case t of
        SPComplexTerm SPEqual [a1, a2]
          | var == a1 -> return a2
          | var == a2 -> return a1
        _ -> fail $ "expecting equation with " ++ show var
             ++ ", got: " ++ showDoc t "") $ splitDisjs frm
  _ -> fail $ "expecting simple quantified disjunction, got: "
       ++ showDoc trm ""

createDomain :: CASLSign -> RMap -> [SPTerm] -> Result (FORMULA ())
createDomain sign m l = do
  let es = map ((\ (e, _, s) -> (e, s)) . typeCheckTerm sign Nothing m) l
  tys <- mapM (\ (e, ms) -> case ms of
          Just s -> return s
          _ -> fail $ unlines e) es
  cs <- mapM (\ ds -> do
        ts@(trm : r) <- mapM (toTERM m . snd) ds
        let mtys = keepMinimals sign id . Set.toList . foldl1 Set.intersection
                  $ map (\ (ty, _) -> Set.insert ty $ supersortsOf ty sign) ds
        case mtys of
          [] -> fail $ "no common supersort found for: " ++ showDoc ds ""
          ty : _ -> do
            let v = mkVarDeclStr "X" ty
            return $ mkForall [v]
              $ if null r then mkStEq (toQualVar v) trm else
                   disjunct $ map (mkStEq $ toQualVar v) ts)
    . Rel.partList
      (on (haveCommonSupersorts True sign) fst) $ zip tys l
  return $ conjunct cs

typeCheckForm :: Bool -> CASLSign -> RMap -> SPTerm -> ([String], RMap)
typeCheckForm rev sign m trm =
  let srts = sortSet sign
      aty = if Set.size srts == 1 then Just $ Set.findMin srts else Nothing
  in case trm of
    SPQuantTerm _ vars frm -> let
        vs = concatMap getVars vars
        rm = foldr Map.delete m vs
        (errs, nm) = typeCheckForm rev sign rm frm
        m2 = foldr Map.delete nm vs
        in (errs, Map.union m m2)
    SPComplexTerm SPEqual [a1, a2] -> let
        (r1, m1, ety) = typeCheckEq sign aty m a1 a2
        in case ety of
             Nothing -> (r1, m1)
             Just _ -> let
               (r2, m2, _) = typeCheckEq sign ety m1 a2 a1
               in (r2, m2)
    SPComplexTerm (SPCustomSymbol cst) args ->
        case Map.lookup cst m of
          Just (CPred pt, _) | length args == length (predArgs pt) ->
            foldl (\ (b, p) (s, a) -> let
                     (nb, nm, _) = typeCheckTerm sign (Just s) p a
                     in (b ++ nb, nm))
                      ([], m) $ zip (predArgs pt) args
          _ -> (["unknown predicate: " ++ show cst], m)
    SPComplexTerm _ args ->
      foldl (\ (b, p) a -> let
           (nb, nm) = typeCheckForm rev sign p a
           in (b ++ nb, nm)) ([], m) $ if rev then reverse args else args

typeCheckEq :: CASLSign -> Maybe SORT -> RMap -> SPTerm -> SPTerm
  -> ([String], RMap, Maybe SORT)
typeCheckEq sign aty m a1 a2 = let
    (r1, m1, ty1) = typeCheckTerm sign aty m a1
    (r2, m2, ty2) = typeCheckTerm sign aty m1 a2
    in case (ty1, ty2) of
             (Just s1, Just s2) ->
                (r1 ++ r2
                 ++ [ "different types " ++ show (s1, s2) ++ " in equation: "
                      ++ showDoc a1 " = " ++ showDoc a2 ""
                    | not $ haveCommonSupersorts True sign s1 s2], m2, Nothing)
             (Nothing, _) -> (r1, m2, ty2)
             (_, Nothing) -> (r1 ++ r2, m2, ty1)

typeCheckTerm :: CASLSign -> Maybe SORT -> RMap -> SPTerm
  -> ([String], RMap, Maybe SORT)
typeCheckTerm sign ty m trm =
  let srts = sortSet sign
      aty = if Set.size srts == 1 then Just $ Set.findMin srts else Nothing
  in case trm of
    SPComplexTerm (SPCustomSymbol cst) args -> case Map.lookup cst m of
      Nothing -> let
          (fb, fm, aTys) = foldr (\ a (b, p, tys) -> let
                     (nb, nm, tya) = typeCheckTerm sign aty p a
                     in (b ++ nb, nm, tya : tys)) ([], m, []) args
          in case ty of
               Just r | all isJust aTys ->
                 if null args && isVar cst then
                     (fb, Map.insert cst (CVar r, Nothing) fm, ty)
                 else (fb, Map.insert cst
                        (COp $ mkTotOpType (catMaybes aTys) r, Nothing) fm
                      , ty)
               _ -> (["no type for: " ++ showDoc trm ""], fm, ty)
      Just (COp ot, _) -> let
          aTys = opArgs ot
          rTy = opRes ot
          (fb, fm) = foldl (\ (b, p) (s, a) -> let
                     (nb, nm, _) = typeCheckTerm sign (Just s) p a
                     in (b ++ nb, nm)) ([], m) $ zip aTys args
          aTyL = length aTys
          argL = length args
          in (fb ++
              ["expected " ++ show aTyL ++ " arguments, but found "
               ++ show argL ++ " for: " ++ show cst | aTyL /= argL]
              ++ case ty of
              Just r -> ["expected result sort " ++ show r ++ ", but found "
                ++ show rTy ++ " for: " ++ show cst | not $ leqSort sign rTy r ]
              _ -> [], fm, Just rTy)
      Just (CVar s2, _) ->
        (["unexpected arguments for variable: " ++ show cst | not $ null args]
         ++ case ty of
              Just r -> ["expected variable sort " ++ show r ++ ", but found "
                ++ show s2 ++ " for: " ++ show cst | not $ leqSort sign s2 r ]
              _ -> [], m, Just s2)
      _ -> (["unexpected predicate in term: " ++ showDoc trm ""], m, ty)
    _ -> (["unexpected term: " ++ showDoc trm ""], m, ty)

toForm :: Monad m => CASLSign -> RMap -> SPTerm -> m (FORMULA ())
toForm sign m t = case t of
    SPQuantTerm q vars frm -> do
        let vs = concatMap getVars vars
            rm = foldr Map.delete m vs
            (b, nm) = typeCheckForm False sign rm frm
            nvs = mapMaybe (toVar nm) vars
        nf <- toForm sign nm frm
        if null b then return $ Quantification (toQuant q) nvs nf nullRange
           else fail $ unlines b
    SPComplexTerm SPEqual [a1, a2] -> do
        t1 <- toTERM m a1
        t2 <- toTERM m a2
        return $ mkStEq t1 t2
    SPComplexTerm (SPCustomSymbol cst) args ->
        case Map.lookup cst m of
          Just (CPred pt, mi) | length args == length (predArgs pt) -> do
              ts <- mapM (toTERM m) args
              case mi of
                Nothing -> case args of
                  [_] -> return trueForm
                  _ -> fail $ "unkown predicate: " ++ show cst
                Just i -> return $ mkPredication
                      (mkQualPred i $ toPRED_TYPE pt) ts
          _ -> fail $ "inconsistent pred symbol: " ++ show cst
    SPComplexTerm symb args -> do
         fs <- mapM (toForm sign m) args
         case (symb, fs) of
           (SPNot, [f]) -> return (mkNeg f)
           (SPImplies, [f1, f2]) -> return (mkImpl f1 f2)
           -- During parsing, "f2 if f1" is saved as "Relation f1 RevImpl f2 _"
           (SPImplied, [f2, f1]) -> return (Relation f1 RevImpl f2 nullRange)
           (SPEquiv, [f1, f2]) -> return (mkEqv f1 f2)
           (SPAnd, _) -> return (conjunct fs)
           (SPOr, _) -> return (disjunct fs)
           (SPTrue, []) -> return trueForm
           (SPFalse, []) -> return falseForm
           _ -> fail $ "wrong boolean formula: " ++ showDoc t ""

toTERM :: Monad m => RMap -> SPTerm -> m (TERM ())
toTERM m spt = case spt of
  SPComplexTerm (SPCustomSymbol cst) args -> case Map.lookup cst m of
    Just (CVar s, _) | null args -> return $ Qual_var cst s nullRange
    Just (COp ot, mi) | length args == length (opArgs ot) -> do
      ts <- mapM (toTERM m) args
      return $ Application (Qual_op_name (case mi of
              Just i -> i
              _ -> simpleIdToId cst) (toOP_TYPE ot) nullRange)
        ts nullRange
    _ -> fail $ "cannot reconstruct term: " ++ showDoc spt ""
  _ -> fail $ "cannot reconstruct term: " ++ showDoc spt ""

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

isVar :: SPIdentifier -> Bool
isVar cst = case tokStr cst of
    c : _ -> isUpper c
    "" -> error "isVar"

getVars :: SPTerm -> [SPIdentifier]
getVars tm = case tm of
    SPComplexTerm (SPCustomSymbol cst) args ->
        if null args then [cst] else concatMap getVars args
    _ -> []

{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2TopSort.hs
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Coding out subsorting into unary predicates.
   New concept for proving Ontologies.

generatedness via non-injective datatype constructors
(i.e. proper data constructors) is simply ignored

total functions my become partial because i.e. division is total
for a second non-zero argument but partial otherwise.

partial functions remain partial unless they fall to together
with an overloaded total function
-}

module Comorphisms.CASL2TopSort (CASL2TopSort (..)) where

import Data.Ord
import Data.Maybe
import Data.List

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.StaticAna (sortsOfArgs)
import CASL.Morphism
import CASL.Sublogic as SL

import qualified Data.Map as Map
import qualified Data.Set as Set

-- | The identity of the comorphism
data CASL2TopSort = CASL2TopSort deriving Show

instance Language CASL2TopSort where
  language_name CASL2TopSort = "CASL2PCFOLTopSort"

instance Comorphism CASL2TopSort
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic CASL2TopSort = CASL
    sourceSublogic CASL2TopSort = SL.caslTop
        { sub_features = LocFilSub
        , cons_features = emptyMapConsFeature }
    targetLogic CASL2TopSort = CASL
    mapSublogic CASL2TopSort sub =
        if sub `isSubElem` sourceSublogic CASL2TopSort
        then Just $
         sub { sub_features = NoSub      -- subsorting is coded out
             , cons_features = NoSortGen -- special Sort_gen_ax is coded out
             , which_logic = max Horn (which_logic sub)
             , has_eq = True             {- was in the original targetLogic
               may be avoided through predications of sort-preds
               with the result terms of functions instead of formulas like:
               forall x : T . bot = x => a(x)
               better: . a(bot) -}
             , has_pred = True
             , has_part = True }
             {- subsorting is coded out and
             special Sort_gen_ax are coded out -}
        else Nothing

    map_theory CASL2TopSort = mkTheoryMapping transSig transSen
    map_morphism CASL2TopSort mor = do
        let trSig = fmap fst . transSig
        sigSour <- trSig $ msource mor
        sigTarg <- trSig $ mtarget mor
        return mor
          { msource = sigSour
          , mtarget = sigTarg }
    map_sentence CASL2TopSort = transSen
    map_symbol CASL2TopSort _ = Set.singleton . id
    has_model_expansion CASL2TopSort = True

data PredInfo = PredInfo { topSortPI :: SORT
                         , directSuperSortsPI :: Set.Set SORT
                         , predicatePI :: PRED_NAME
                         } deriving Show

type SubSortMap = Map.Map SORT PredInfo

generateSubSortMap :: Rel.Rel SORT -> PredMap -> SubSortMap
generateSubSortMap sortRels pMap =
    let disAmbMap = Map.map disAmbPred
        disAmbPred v = let pn = predicatePI v in
          case dropWhile (`Set.member` MapSet.keysSet pMap)
                   $ pn : map (\x -> appendString (predicatePI v) $ show x) 
                          [1::Int ..] of
            n : _ -> v { predicatePI = n }
            [] -> error "generateSubSortMap"
        mR = (Rel.flatSet .
              Rel.partSet (\ x y -> Rel.member x y sortRels &&
                                    Rel.member y x sortRels))
             (Rel.mostRight sortRels)
        toPredInfo k e =
            let ts = case filter (flip (Rel.member k) sortRels)
                     $ Set.toList mR of
                     [x] -> x
                     _ -> error "CASL2TopSort.generateSubSortMap.toPredInfo"
            in PredInfo { topSortPI = ts
                        , directSuperSortsPI = Set.difference e mR
                        , predicatePI = k }
        initMap = Map.filterWithKey (\ k _ -> not $ Set.member k mR)
            (Map.mapWithKey toPredInfo
                   (Rel.toMap (Rel.intransKernel sortRels)))
    in disAmbMap initMap

{- | Finds Top-sort(s) and transforms for each top-sort all subsorts
into unary predicates. All predicates typed with subsorts are now
typed with the top-sort and axioms reflecting the typing are
generated. The operations are treated analogous. Axioms are
generated that each generated unary predicate must hold on at least
one element of the top-sort. -}

transSig :: Sign () e -> Result (Sign () e, [Named (FORMULA ())])
transSig sig = return
  $ let sortRels = Rel.rmNullSets $ sortRel sig in
    if Rel.nullKeys sortRels then (sig, []) else
    let subSortMap = generateSubSortMap sortRels (predMap sig)
        newOpMap = transOpMap sortRels subSortMap (opMap sig)
        newAssOpMap0 = transOpMap sortRels subSortMap (assocOps sig)
        axs = generateAxioms subSortMap (predMap sig) newOpMap
        newPreds = foldr (\ pI -> MapSet.insert (predicatePI pI)
                          $ PredType [topSortPI pI])
                    MapSet.empty . Map.elems
        newPredMap = MapSet.union (transPredMap subSortMap
                  $ predMap sig) $ newPreds subSortMap
    in (sig
        { sortRel = Rel.fromKeysSet
            $ Set.fromList (map topSortPI $ Map.elems subSortMap)
              `Set.union` (sortSet sig `Set.difference` Map.keysSet subSortMap)
        , opMap = newOpMap
        , assocOps = interOpMapSet newAssOpMap0 newOpMap
        , predMap = newPredMap
        }, axs ++ symmetryAxioms subSortMap sortRels)

transPredMap :: SubSortMap -> PredMap -> PredMap
transPredMap subSortMap = MapSet.map transType
    where transType t = t
            { predArgs = map (lkupTop subSortMap) $ predArgs t }

transOpMap :: Rel.Rel SORT -> SubSortMap -> OpMap -> OpMap
transOpMap sRel subSortMap = rmOrAddPartsMap True . MapSet.map transType
    where
          transType t =
              let args = opArgs t
                  lkp = lkupTop subSortMap
                  newArgs = map lkp args
                  kd = opKind t
              in -- make function partial if argument sorts are subsorts
              t { opArgs = map lkp $ opArgs t
                , opRes = lkp $ opRes t
                , opKind = if kd == Total && and (zipWith
                           (\ a na -> a == na || Rel.member na a sRel)
                           args newArgs) then kd else Partial }

procOpMapping :: SubSortMap -> OP_NAME -> Set.Set OpType
  -> [Named (FORMULA ())] -> [Named (FORMULA ())]
procOpMapping subSortMap opName =
  (++) . Map.foldrWithKey procProfMapOpMapping [] . mkProfMapOp subSortMap
  where
    procProfMapOpMapping :: [SORT] -> (OpKind, Set.Set [Maybe PRED_NAME])
                         -> [Named (FORMULA ())] -> [Named (FORMULA ())]
    procProfMapOpMapping sl (kind, spl) = genArgRest
        (genSenName "o" opName $ length sl) (genOpEquation kind opName) sl spl

mkSimpleQualPred :: PRED_NAME -> SORT -> PRED_SYMB
mkSimpleQualPred symS ts = mkQualPred symS $ Pred_type [ts] nullRange

symmetryAxioms :: SubSortMap -> Rel.Rel SORT -> [Named (FORMULA ())]
symmetryAxioms ssMap sortRels =
    let symSets = Rel.sccOfClosure sortRels
        toAxioms = concatMap
          (\ s ->
            let ts = lkupTop ssMap s
                symS = lkupPred ssMap s
                psy = mkSimpleQualPred symS ts
                vd = mkVarDeclStr "x" ts
                vt = toQualVar vd
            in if ts == s then [] else
                   [makeNamed (show ts ++ "_symmetric_with_" ++ show symS)
                   $ mkForall [vd] $ mkPredication psy [vt]]
          ) . Set.toList
    in concatMap toAxioms symSets

generateAxioms :: SubSortMap -> PredMap -> OpMap -> [Named (FORMULA ())]
generateAxioms subSortMap pMap oMap = hi_axs ++ p_axs ++ axs
    where -- generate argument restrictions for operations
          axs = Map.foldrWithKey (procOpMapping subSortMap) []
                $ MapSet.toMap oMap
          p_axs =
          -- generate argument restrictions for predicates
           Map.foldrWithKey (\ pName ->
              (++) . Map.foldrWithKey
                             (\ sl -> genArgRest
                                      (genSenName "p" pName $ length sl)
                                      (genPredication pName)
                                      sl)
                                    [] . mkProfMapPred subSortMap)
                   [] $ MapSet.toMap pMap
          hi_axs =
          {- generate subclass_of axioms derived from subsorts
          and non-emptyness axioms -}
              concatMap (\ prdInf ->
               let ts = topSortPI prdInf
                   subS = predicatePI prdInf
                   set = directSuperSortsPI prdInf
                   supPreds = map (lkupPred subSortMap) $ Set.toList set
                   x = mkVarDeclStr "x" ts
                   mkPredf sS = mkPredication (mkSimpleQualPred sS ts)
                     [toQualVar x]
                in makeNamed (show subS ++ "_non_empty")
                   (Quantification Existential [x] (mkPredf subS)
                     nullRange)
                   : map (\ supS ->
                       makeNamed (show subS ++ "_subclassOf_" ++ show supS)
                       $ mkForall [x]
                          $ mkImpl (mkPredf subS) $ mkPredf supS)
                         supPreds
             ) $ Map.elems subSortMap

mkProfMapPred :: SubSortMap -> Set.Set PredType
              -> Map.Map [SORT] (Set.Set [Maybe PRED_NAME])
mkProfMapPred ssm = Set.fold seperate Map.empty
    where seperate pt = MapSet.setInsert (pt2topSorts pt) (pt2preds pt)
          pt2topSorts = map (lkupTop ssm) . predArgs
          pt2preds = map (lkupPredM ssm) . predArgs

mkProfMapOp :: SubSortMap -> Set.Set OpType
            -> Map.Map [SORT] (OpKind, Set.Set [Maybe PRED_NAME])
mkProfMapOp ssm = Set.fold seperate Map.empty
    where seperate ot =
              Map.insertWith (\ (k1, s1) (k2, s2) ->
                                           (min k1 k2, Set.union s1 s2))
                (pt2topSorts joinedList)
                (fKind, Set.singleton $ pt2preds joinedList)
              where joinedList = opSorts ot
                    fKind = opKind ot
                    pt2topSorts = map (lkupTop ssm)
                    pt2preds = map (lkupPredM ssm)

lkupTop :: SubSortMap -> SORT -> SORT
lkupTop ssm s = maybe s topSortPI (Map.lookup s ssm)

lkupPredM :: SubSortMap -> SORT -> Maybe PRED_NAME
lkupPredM ssm s = fmap predicatePI $ Map.lookup s ssm

lkupPred :: SubSortMap -> SORT -> PRED_NAME
lkupPred ssm = fromMaybe (error "CASL2TopSort.lkupPred") . lkupPredM ssm

genArgRest :: String -> ([VAR_DECL] -> FORMULA f)
               {- ^ generates from a list of variables
               either the predication or function equation -}
           -> [SORT] -> Set.Set [Maybe PRED_NAME]
           -> [Named (FORMULA f)] -> [Named (FORMULA f)]
genArgRest sen_name genProp sl spl fs =
    let vars = genVars sl
        mquant = genQuantification (genProp vars) vars spl
    in maybe fs (\ quant -> makeNamed sen_name quant : fs) mquant

genPredication :: PRED_NAME -> [VAR_DECL] -> FORMULA f
genPredication pName vars =
  genPredAppl pName (map (\ (Var_decl _ s _) -> s) vars) $ map toQualVar vars

-- | generate a predication with qualified pred name
genPredAppl :: PRED_NAME -> [SORT] -> [TERM f] -> FORMULA f
genPredAppl pName sl terms = Predication (Qual_pred_name pName
    (Pred_type sl nullRange) nullRange) terms nullRange

genOpEquation :: OpKind -> OP_NAME -> [VAR_DECL] -> FORMULA f
genOpEquation kind opName vars = case vars of
  resV@(Var_decl _ s _) : argVs -> mkStEq opTerm resTerm
    where opTerm = mkAppl (mkQualOp opName opType) argTerms
          opType = Op_type kind argSorts s nullRange
          argSorts = sortsOfArgs argVs
          resTerm = toQualVar resV
          argTerms = map toQualVar argVs
  _ -> error "CASL2TopSort.genOpEquation: no result variable"

genVars :: [SORT] -> [VAR_DECL]
genVars = zipWith mkVarDeclStr varSymbs
    where varSymbs =
            map (: []) "xyzuwv" ++ map (\ i -> 'v' : show i) [(1 :: Int) ..]

genSenName :: Show a => String -> a -> Int -> String
genSenName suff symbName arity =
    "arg_rest_" ++ show symbName ++ '_' : suff ++ '_' : show arity

genQuantification :: FORMULA f {- ^ either the predication or
                               function equation -}
                  -> [VAR_DECL] -- ^ Qual_vars
                  -> Set.Set [Maybe PRED_NAME]
                  -> Maybe (FORMULA f)
genQuantification prop vars spl = do
     dis <- genDisjunction vars spl
     return $ mkForall vars $ mkImpl prop dis

genDisjunction :: [VAR_DECL] -> Set.Set [Maybe PRED_NAME] -> Maybe (FORMULA f)
genDisjunction vars spn
    | Set.size spn == 1 =
        case disjs of
        [] -> Nothing
        [x] -> Just x
        _ -> error "CASL2TopSort.genDisjunction: this cannot happen"
    | null disjs = Nothing
    | otherwise = Just (disjunct disjs)
      where disjs = foldl genConjunction [] (Set.toList spn)
            genConjunction acc pns
                | null conjs = acc
                | otherwise = conjunct (reverse conjs) : acc
                where conjs = foldl genPred [] (zip vars pns)
            genPred acc (v, mpn) = maybe acc
                (\ pn -> genPredication pn [v] : acc) mpn

{- | Each membership test of a subsort is transformed to a predication
of the corresponding unary predicate. Variables quantified over a
subsort yield a premise to the quantified formula that the
corresponding predicate holds. All typings are adjusted according
to the subsortmap and sort generation constraints are translated to
disjointness axioms. -}

transSen :: Sign f e -> FORMULA f -> Result (FORMULA f)
transSen sig f = let sortRels = Rel.rmNullSets $ sortRel sig in
    if Rel.noPairs sortRels then return f else do
    let ssm = generateSubSortMap sortRels (predMap sig)
        newOpMap = transOpMap sortRels ssm (opMap sig)
    mapSen ssm newOpMap f

mapSen :: SubSortMap -> OpMap -> FORMULA f -> Result (FORMULA f)
mapSen ssMap opM f =
    case f of
    Sort_gen_ax cs _ ->
        genEitherAxiom ssMap cs
    _ -> return $ foldFormula (mapRec ssMap opM) f

mapRec :: SubSortMap -> OpMap -> Record f (FORMULA f) (TERM f)
mapRec ssM opM = (mapRecord id)
  { foldQuantification = \ _ q vdl ->
        Quantification q (map updateVarDecls vdl) . relativize q vdl
  , foldMembership = \ _ t s pl -> maybe (Membership t s pl)
      (\ pn -> genPredAppl pn [lTop s] [t]) $ lPred s
  , foldPredication = \ _ -> Predication . updatePRED_SYMB
  , foldQual_var = \ _ v -> Qual_var v . lTop
  , foldApplication = \ _ -> Application . updateOP_SYMB
  , foldSorted_term = \ _ t1 -> Sorted_term t1 . lTop
    -- casts are discarded due to missing subsorting
  , foldCast = \ _ t1 _ _ -> t1 }
    where lTop = lkupTop ssM
          lPred = lkupPredM ssM
          updateOP_SYMB (Op_name _) =
              error "CASL2TopSort.mapTerm: got untyped application"
          updateOP_SYMB (Qual_op_name on ot pl) =
              Qual_op_name on (updateOP_TYPE on ot) pl
          updateOP_TYPE on (Op_type _ sl s pl) =
              let args = map lTop sl
                  res = lTop s
                  t1 = toOpType $ Op_type Total args res pl
                  ts = MapSet.lookup on opM
                  nK = if Set.member t1 ts then Total else Partial
              in Op_type nK args res pl
          updateVarDecls (Var_decl vl s pl) =
              Var_decl vl (lTop s) pl
          updatePRED_SYMB (Pred_name _) =
              error "CASL2TopSort.mapSen: got untyped predication"
          updatePRED_SYMB (Qual_pred_name pn (Pred_type sl pl') pl) =
              Qual_pred_name pn
                 (Pred_type (map lTop sl) pl') pl
          -- relativize quantifiers using predicates coding sorts
          relativize q vdl f1 = let vPs = mkVarPreds vdl in
              if null vdl then f1
              else case q of  -- universal? then use implication
                Universal -> mkImpl vPs f1
                -- existential or unique-existential? then use conjuction
                _ -> conjunct [vPs, f1]
          mkVarPreds = conjunct . map mkVarPred
          mkVarPred (Var_decl vs s _) = conjunct $ foldr (mkVarPred1 s) [] vs
          mkVarPred1 s v = case lPred s of
                 -- no subsort? then no relativization
                 Nothing -> id
                 Just p1 -> (genPredication p1 [mkVarDecl v $ lTop s] :)

genEitherAxiom :: SubSortMap -> [Constraint] -> Result (FORMULA f)
genEitherAxiom ssMap =
    genConjunction . (\ (_, osl, _) -> osl) . recover_Sort_gen_ax
    where genConjunction osl =
            let (injOps, constrs) = partition isInjOp osl
                groupedInjOps = groupBy sameTarget $ sortBy compTarget injOps
            in if null constrs
               then case groupedInjOps of
                    [] -> fatal_error "No injective operation found" nullRange
                    [xs@(x : _)] -> return $ genQuant x $ genImpl xs
                    ((x : _) : _) -> return $ genQuant x
                        $ conjunct $ map genImpl groupedInjOps
                    _ -> error "CASL2TopSort.genEitherAxiom.groupedInjOps"
               else Result [mkDiag Hint
                            "ignoring generating constructors"
                            constrs]
                    $ Just trueForm
          isInjOp ops =
              case ops of
              Op_name _ -> error "CASL2TopSort.genEitherAxiom.isInjObj"
              Qual_op_name on _ _ -> isInjName on
          resultSort (Qual_op_name _ (Op_type _ _ t _) _) = t
          resultSort _ = error "CASL2TopSort.genEitherAxiom.resultSort"
          argSort (Qual_op_name _ (Op_type _ [x] _ _) _) = x
          argSort _ = error "CASL2TopSort.genEitherAxiom.argSort"
          compTarget = comparing resultSort
          sameTarget x1 x2 = compTarget x1 x2 == EQ
          lTop = lkupTop ssMap
          mkXVarDecl = mkVarDeclStr "x" . lTop . resultSort
          genQuant qon = mkForall [mkXVarDecl qon]
          genImpl xs = case xs of
            x : _ -> let
              rSrt = resultSort x
              ltSrt = lTop rSrt
              disjs = genDisj xs
              in if ltSrt == lTop (argSort x) then
                   if rSrt == ltSrt then disjs else mkImpl (genProp x) disjs
                 else error "CASL2TopSort.genEitherAxiom.genImpl"
            _ -> error "CASL2TopSort.genEitherAxiom.genImpl No OP_SYMB found"
          genProp qon =
              genPredication (lPredName $ resultSort qon) [mkXVarDecl qon]
          lPredName = lkupPred ssMap
          genDisj qons = disjunct (map genPred qons)
          genPred qon =
              genPredication (lPredName $ argSort qon) [mkXVarDecl qon]

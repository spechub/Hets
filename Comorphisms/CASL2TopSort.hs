{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Coding out subsorting into unary predicates.
   New concept for proving Ontologies.
-}

module Comorphisms.CASL2TopSort (CASL2TopSort(..)) where

import Control.Exception (assert)

import Data.Maybe
import Data.List

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import Common.Result
import qualified Common.Lib.Rel as Rel

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
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
    sourceSublogic CASL2TopSort = SL.top
        { sub_features = LocFilSub
        , which_logic = FOL
        , cons_features = SortGen
            { emptyMapping = True
            , onlyInjConstrs = True }}
    targetLogic CASL2TopSort = CASL
    mapSublogic CASL2TopSort sub =
        if sub `isSubElem` sourceSublogic CASL2TopSort
        then Just $
         sub { sub_features = NoSub      -- subsorting is coded out
             , cons_features = NoSortGen -- special Sort_gen_ax is coded out
             , which_logic = max Horn (which_logic sub)
             , has_eq = True             -- was in the original targetLogic
               -- may be avoided through predications of sort-preds
               -- with the result terms of functions instead of formulas like:
               -- forall x : T . bot = x => a(x)
               -- better: . a(bot)
             , has_pred = True }
             -- subsorting is coded out and
             -- special Sort_gen_ax are coded out
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

data PredInfo = PredInfo { topSortPI    :: SORT
                         , directSuperSortsPI :: Set.Set SORT
                         , predicatePI  :: PRED_NAME
                         } deriving (Show, Ord, Eq)

type SubSortMap = Map.Map SORT PredInfo

generateSubSortMap :: Rel.Rel SORT
                   -> Map.Map Id (Set.Set PredType)
                   -> Result SubSortMap
generateSubSortMap sortRels pMap =
    let disAmbMap = Map.map disAmbPred
        disAmbPred v = if Map.member (predicatePI v) pMap
                       then disAmbPred' (1::Int) v'
                       else v
            where v' = add "_s" v
                  disAmbPred' x v1 =
                      if Map.member (predicatePI v1) pMap
                      then disAmbPred' (x + 1) (add (show x) v')
                      else v1
                  add s v1 = v1 {predicatePI =
                                   case predicatePI v1 of
                                   Id ts is ps ->
                                      assert (not (null ts))
                                         (Id (init ts ++
                                              [(last ts) {tokStr =
                                                          tokStr (last ts)++s}
                                              ]) is ps)
                                }
        mR = (Rel.flatSet .
              Rel.partSet (\ x y -> Rel.member x y sortRels &&
                                    Rel.member y x sortRels))
             (Rel.mostRight sortRels)
        toPredInfo k e =
            let ts = case filter (\pts -> Rel.member k pts sortRels)
                     $ Set.toList mR of
                     [x] -> x
                     _ -> error "CASL2TopSort.generateSubSortMap.toPredInfo"
            in PredInfo { topSortPI = ts
                        , directSuperSortsPI = Set.difference e mR
                        , predicatePI = k }
        initMap = Map.filterWithKey (\k _ -> not (Set.member k mR))
            (Map.mapWithKey toPredInfo
                   (Rel.toMap (Rel.intransKernel sortRels)))
    in return (disAmbMap initMap)

-- | Finds Top-sort(s) and transforms for each top-sort all subsorts
-- into unary predicates. All predicates typed with subsorts are now
-- typed with the top-sort and axioms reflecting the typing are
-- generated. The operations are treated analogous. Axioms are
-- generated that each generated unary predicate must hold on at least
-- one element of the top-sort.

transSig :: Sign () e -> Result (Sign () e, [Named (FORMULA ())])
transSig sig = if Rel.null sortRels then
        hint (sig, [])
        "CASL2TopSort.transSig: Signature is unchanged (no subsorting present)"
        nullRange
    else do
    subSortMap <- generateSubSortMap sortRels (predMap sig)
    let (dias2, newPredMap) = Map.mapAccum (\ ds (un, ds1) -> (ds ++ ds1, un))
          [] $ Map.unionWithKey repError (transPredMap subSortMap
                  $ predMap sig) $ newPreds subSortMap
    Result dias2 $ Just ()
    axs <- generateAxioms subSortMap (predMap sig) (opMap sig)
    return (sig
        { sortSet = Set.fromList (map topSortPI $ Map.elems subSortMap)
              `Set.union` (sortSet sig `Set.difference` Map.keysSet subSortMap)
        , sortRel = Rel.empty
        , opMap   = transOpMap subSortMap (opMap sig)
        , assocOps= transOpMap subSortMap (assocOps sig)
        , predMap = newPredMap
        }, axs ++ symmetryAxioms subSortMap sortRels)
    where sortRels = Rel.transClosure $ sortRel sig
          repError k (v1, d1) (v2, d2) =
              (Set.union v1 v2,
               Diag Warning
                     ("CASL2TopSort.transSig: generating " ++
                      "overloading: Predicate " ++ show k ++
                      " gets additional type(s): " ++ show v2) nullRange
               : d1 ++ d2 )
          newPreds =
              foldr (\ pI -> Map.insert (predicatePI pI)
                                           (Set.singleton
                                            (PredType [topSortPI pI]),[]))
                    Map.empty . Map.elems

transPredMap :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType)
             -> Map.Map PRED_NAME (Set.Set PredType, [Diagnosis])
transPredMap subSortMap = Map.map (\ s -> (Set.map transType s, []))
    where transType t = t
            { predArgs = map (\ s -> maybe s topSortPI
                             $ Map.lookup s subSortMap) $ predArgs t }

transOpMap :: SubSortMap -> Map.Map OP_NAME (Set.Set OpType)
           -> Map.Map OP_NAME (Set.Set OpType)
transOpMap subSortMap = Map.map (tidySet . Set.map transType)
    where tidySet s = Set.fold joinPartial s s
            where joinPartial t@(OpType {opKind = Partial})
                      | Set.member t {opKind = Total} s = Set.delete t
                      | otherwise = id
                  joinPartial _ = id
          transType t =
              t { opArgs = map lkp (opArgs t)
                , opRes = lkp (opRes t)}
          lkp s = maybe s topSortPI (Map.lookup s subSortMap)

procOpMapping :: SubSortMap
              -> OP_NAME -> Set.Set OpType
              -> Result [Named (FORMULA ())] -> Result [Named (FORMULA ())]
procOpMapping subSortMap opName set r = do
    al <- r
    profMap <- mkProfMapOp opName subSortMap set
    return $ al ++ Map.foldWithKey procProfMapOpMapping [] profMap
  where
    procProfMapOpMapping :: [SORT] -> (OpKind, Set.Set [Maybe PRED_NAME])
                         -> [Named (FORMULA ())] -> [Named (FORMULA ())]
    procProfMapOpMapping sl (kind, spl) = genArgRest
        (genSenName "o" opName $ length sl) (genOpEquation kind opName) sl spl

mkQualPred :: PRED_NAME -> SORT -> PRED_SYMB
mkQualPred symS ts = Qual_pred_name symS (Pred_type [ts] nullRange) nullRange

symmetryAxioms :: SubSortMap -> Rel.Rel SORT -> [Named (FORMULA ())]
symmetryAxioms ssMap sortRels =
    let symSets = Rel.sccOfClosure sortRels
        mR = Rel.mostRight sortRels
        symTopSorts = not . Set.null . Set.intersection mR
        toAxioms symSet = map (\ s ->
            let ts = lkupTop ssMap s
                Just symS = lkupPredName ssMap s
                psy = mkQualPred symS ts
                vd = mkVarDeclStr "x" ts
                vt = toQualVar vd
            in makeNamed (show ts ++ "_symmetric_with_" ++ show symS)
                   $ mkForall [vd] (Predication psy [vt] nullRange) nullRange
            ) $ Set.toList (Set.difference symSet mR)
    in concatMap toAxioms (filter symTopSorts symSets)

generateAxioms :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType)
               -> Map.Map OP_NAME (Set.Set OpType)
               -> Result [Named (FORMULA ())]
generateAxioms subSortMap pMap oMap = do
    -- generate argument restrictions for operations
    axs <- Map.foldWithKey (procOpMapping subSortMap) (return []) oMap
    return $ hi_axs ++ reverse p_axs ++ reverse axs
    where p_axs =
          -- generate argument restrictions for predicates
           Map.foldWithKey (\ pName set ->
              (++ Map.foldWithKey
                             (\ sl -> genArgRest
                                      (genSenName "p" pName $ length sl)
                                      (genPredication pName)
                                      sl)
                                    [] (mkProfMapPred subSortMap set)))
                   [] pMap
          hi_axs =
          -- generate subclass_of axioms derived from subsorts
          -- and non-emptyness axioms
              concatMap (\ prdInf ->
               let ts = topSortPI prdInf
                   subS = predicatePI prdInf
                   set = directSuperSortsPI prdInf
                   supPreds =
                     map (\ s ->
                            maybe (error ("CASL2TopSort: genAxioms:" ++
                                   " impossible happend: " ++ show s))
                                  predicatePI $ Map.lookup s subSortMap)
                         $ Set.toList set
                   x = mkVarDeclStr "x" ts
                   mkPredf sS = Predication (mkQualPred sS ts) [toQualVar x]
                                nullRange
                in makeNamed (show subS ++ "_non_empty")
                   (Quantification Existential [x] (mkPredf subS)
                     nullRange)
                   : map (\ supS ->
                       makeNamed (show subS ++ "_subclassOf_" ++ show supS)
                       $ mkForall [x]
                          (mkImpl (mkPredf subS) $ mkPredf supS)
                          nullRange) supPreds
             ) $ Map.elems subSortMap

mkProfMapPred :: SubSortMap -> Set.Set PredType
              -> Map.Map [SORT] (Set.Set [Maybe PRED_NAME])
mkProfMapPred ssm = Set.fold seperate Map.empty
    where seperate pt = Rel.setInsert (pt2topSorts pt) (pt2preds pt)
          pt2topSorts = map (lkupTop ssm) . predArgs
          pt2preds = map (lkupPredName ssm) . predArgs

mkProfMapOp :: OP_NAME -> SubSortMap -> Set.Set OpType
              -> Result (Map.Map [SORT] (OpKind, Set.Set [Maybe PRED_NAME]))
mkProfMapOp opName ssm = Set.fold seperate (return Map.empty)
    where seperate ot r = do
              mp <- r
              Result dias' $ Just ()
              return $ Map.insertWith (\ (k1, s1) (k2, s2) ->
                                           (min k1 k2, Set.union s1 s2))
                (pt2topSorts joinedList)
                (fKind, Set.singleton $ pt2preds joinedList) mp
              where joinedList = opArgs ot ++ [opRes ot]
                    fKind = opKind ot
                    dias' = [ Diag Warning
                                        ("Please, check if operation \"" ++
                                         show opName ++
                                         "\" is still partial as intended,\
                                          \ since a joining of types could\
                                         \ have made it total!!")
                                        nullRange
                              | fKind == Partial ]
          pt2topSorts = map (lkupTop ssm)
          pt2preds = map (lkupPredName ssm)

lkupTop :: SubSortMap -> SORT -> SORT
lkupTop ssm s = maybe s topSortPI (Map.lookup s ssm)

lkupPredName :: SubSortMap -> SORT -> Maybe PRED_NAME
lkupPredName ssm s = maybe Nothing (Just . predicatePI) (Map.lookup s ssm)

genArgRest :: String
           -> ([VAR_DECL] -> FORMULA f)
               -- ^ generates from a list of variables
               -- either the predication or function equation
           -> [SORT] -> (Set.Set [Maybe PRED_NAME])
           -> [Named (FORMULA f)] -> [Named (FORMULA f)]
genArgRest sen_name genProp sl spl fs =
    let vars = genVars sl
        mquant = genQuantification (genProp vars) vars spl
    in maybe fs (\ quant -> mapNamed (const quant) (makeNamed "" sen_name)
                             : fs) mquant

genPredication :: PRED_NAME -> [VAR_DECL] -> FORMULA f
genPredication pName vars =
  genPredAppl pName (map (\ (Var_decl _ s _) -> s) vars) $ map toQualVar vars

-- | generate a predication with qualified pred name
genPredAppl :: PRED_NAME -> [SORT] -> [TERM f] -> FORMULA f
genPredAppl pName sl terms = Predication (Qual_pred_name pName
    (Pred_type sl nullRange) nullRange) terms nullRange

genOpEquation :: OpKind -> OP_NAME -> [VAR_DECL] -> FORMULA f
genOpEquation kind opName vars =
    Strong_equation opTerm resTerm nullRange
    where terms = map toQualVar vars
          opTerm = mkAppl (Qual_op_name opName opType nullRange) argTerms
          opType = Op_type kind argSorts resSort nullRange
          argTerms = init terms
          resTerm  = last terms
          argSorts = map sortOfTerm argTerms
          resSort  = sortOfTerm resTerm

genVars :: [SORT] -> [VAR_DECL]
genVars = zipWith mkVarDeclStr varSymbs
    where varSymbs =
            map (: []) "xyzuwv" ++ map (\ i -> 'v' : show i) [(1::Int)..]

genSenName :: Show a => String -> a -> Int -> String
genSenName suff symbName arity =
    "arg_rest_" ++ show symbName ++ '_' : suff ++ '_' : show arity

genQuantification :: FORMULA f -- ^ either the predication or
                               -- function equation
                  -> [VAR_DECL] -- ^ Qual_vars
                  -> (Set.Set [Maybe PRED_NAME])
                  -> Maybe (FORMULA f)
genQuantification prop vars spl = do
     dis <- genDisjunction vars spl
     return $ mkForall vars
                (mkImpl prop dis) nullRange

genDisjunction :: [VAR_DECL] -> Set.Set [Maybe PRED_NAME] -> Maybe (FORMULA f)
genDisjunction vars spn
    | Set.size spn == 1 =
        case disjs of
        []  -> Nothing
        [x] -> Just x
        _   -> error "CASL2TopSort.genDisjunction: this cannot happen"
    | null disjs        = Nothing
    | otherwise         = Just (Disjunction disjs nullRange)
      where disjs = foldl genConjunction [] (Set.toList spn)
            genConjunction acc pns
                | null conjs = acc
                | otherwise  = Conjunction (reverse conjs) nullRange : acc
                where conjs = foldl genPred [] (zip vars pns)
            genPred acc (v, mpn) = maybe acc
                (\ pn -> genPredication pn [v] : acc) mpn

-- | Each membership test of a subsort is transformed to a predication
-- of the corresponding unary predicate. Variables quantified over a
-- subsort yield a premise to the quantified formula that the
-- corresponding predicate holds. All typings are adjusted according
-- to the subsortmap and sort generation constraints are translated to
-- disjointness axioms.

transSen :: (Show f) => Sign f e -> FORMULA f -> Result (FORMULA f)
transSen sig f = let sortRels = Rel.transClosure $ sortRel sig in
    if Rel.null sortRels then
        Result [Diag Hint
        "CASL2TopSort.transSen: Sentence is unchanged (no subsorting present)"
        nullRange ] (Just f)
    else do
    ssm <- generateSubSortMap sortRels (predMap sig)
    mapSen ssm f

mapSen :: SubSortMap -> FORMULA f -> Result (FORMULA f)
mapSen ssMap f =
    case f of
    Sort_gen_ax cs _ ->
        genEitherAxiom ssMap cs
    _ -> return $ mapSen1 ssMap f

mapSen1 :: SubSortMap -> FORMULA f -> FORMULA f
mapSen1 subSortMap f =
    case f of
    Conjunction fl pl -> Conjunction (map (mapSen1 subSortMap) fl) pl
    Disjunction fl pl -> Disjunction (map (mapSen1 subSortMap) fl) pl
    Implication f1 f2 b pl ->
        Implication (mapSen1 subSortMap f1) (mapSen1 subSortMap f2) b pl
    Equivalence f1 f2 pl ->
        Equivalence (mapSen1 subSortMap f1) (mapSen1 subSortMap f2) pl
    Negation f1 pl -> Negation (mapSen1 subSortMap f1) pl
    tr@(True_atom _)  -> tr
    fa@(False_atom _) -> fa
    Quantification q vdl f1 pl ->
        Quantification q (map updateVarDecls vdl)
                         (relativize q vdl (mapSen1 subSortMap f1)) pl
    Membership t s pl ->
        let t' = mapTerm subSortMap t
        in maybe (Membership t' s pl)
                 (\pn -> genPredAppl pn [lkupTop subSortMap s]
                                           [t'])
                 (lkupPredName subSortMap s)
    Existl_equation t1 t2 pl ->
        Existl_equation (mapTerm subSortMap t1) (mapTerm subSortMap t2) pl
    Strong_equation t1 t2 pl ->
        Strong_equation (mapTerm subSortMap t1) (mapTerm subSortMap t2) pl
    Definedness t pl ->
        Definedness (mapTerm subSortMap t) pl
    Predication psy tl pl ->
        Predication (updatePRED_SYMB psy) (map (mapTerm subSortMap) tl) pl
    ExtFORMULA f1 -> ExtFORMULA f1 -- ExtFORMULA stays as it is
    _ ->
        error "CASL2TopSort.mapSen1"
    where updateVarDecls (Var_decl vl s pl) =
              Var_decl vl (lkupTop subSortMap s) pl
          updatePRED_SYMB (Pred_name _) =
              error "CASL2TopSort.mapSen: got untyped predication"
          updatePRED_SYMB (Qual_pred_name pn (Pred_type sl pl') pl) =
              Qual_pred_name pn
                 (Pred_type (map (lkupTop subSortMap) sl) pl') pl
          -- relativize quantifiers using predicates coding sorts
          -- universal? the use implication
          relativize Universal vdl f1 =
              if null vdl then f1
              else mkImpl (mkVarPreds vdl) f1
          -- existential or unique-existential? then use conjuction
          relativize _ vdl f1 =
              if null vdl then f1
              else conjunct [mkVarPreds vdl, f1]
          mkVarPreds = conjunct . map mkVarPred
          mkVarPred (Var_decl vs s _) = conjunct $ map (mkVarPred1 s) vs
          mkVarPred1 s v =
              let sTop = lkupTop subSortMap s
                  p = lkupPredName subSortMap s
              in case p of
                 -- no subsort? then no relativization
                 Nothing -> True_atom nullRange
                 Just p1 -> genPredAppl p1 [sTop] [mkVarTerm v s]


mapTerm :: SubSortMap -> TERM f -> TERM f
mapTerm ssMap t = case t of
    Qual_var v s pl -> Qual_var v (lTop s) pl
    Application osy tl pl ->
        Application (updateOP_SYMB osy) (map (mapTerm ssMap) tl) pl
    Sorted_term t1 s pl ->
        Sorted_term (mapTerm ssMap t1) (lTop s) pl
    -- casts are discarded due to missing subsorting
    Cast t1 _ _ -> mapTerm ssMap t1
    Conditional t1 f t2 pl ->
        Conditional (mapTerm ssMap t1) (mapSen1 ssMap f) (mapTerm ssMap t2) pl
    _ -> error "CASL2TopSort.mapTerm"
    where lTop = lkupTop ssMap
          updateOP_SYMB (Op_name _) =
              error "CASL2TopSort.mapTerm: got untyped application"
          updateOP_SYMB (Qual_op_name on ot pl) =
              Qual_op_name on (updateOP_TYPE ot) pl
          updateOP_TYPE (Op_type fk sl s pl) =
              Op_type fk (map lTop sl) (lTop s) pl

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
               else Result [Diag Error
                                  "CASL2TopSort: Cannot handle \
                                  \datatype constructors; only subsort \
                                  \embeddings are allowed with free and \
                                  \generated types!" nullRange] Nothing
          isInjOp ops =
              case ops of
              Op_name _ -> error "CASL2TopSort.genEitherAxiom.isInjObj"
              Qual_op_name on _ _ -> isInjName on
          resultSort (Qual_op_name _ (Op_type _ _ t _) _) = t
          resultSort _ = error "CASL2TopSort.genEitherAxiom.resultSort"
          argSort (Qual_op_name _ (Op_type _ [x] _ _) _) = x
          argSort _ = error "CASL2TopSort.genEitherAxiom.argSort"
          compTarget x1 x2 = compare (resultSort x1) (resultSort x2)
          sameTarget x1 x2 = compTarget x1 x2 == EQ
          lTop = lkupTop ssMap
          mkXVarDecl = mkVarDeclStr "x" . lTop . resultSort
          genQuant qon f = mkForall [mkXVarDecl qon] f nullRange
          genImpl xs = case xs of
            x : _ -> let
              rSrt = resultSort x
              ltSrt = lTop rSrt
              disjs = genDisj xs
              in if ltSrt == lTop (argSort x) then
                   if rSrt == ltSrt then disjs else mkImpl (genProp x) disjs
                 else  error "CASL2TopSort.genEitherAxiom.genImpl"
            _ -> error "CASL2TopSort.genEitherAxiom.genImpl No OP_SYMB found"
          genProp qon =
              genPredication (lPredName $ resultSort qon) [mkXVarDecl qon]
          lPredName s = fromMaybe (error $
              "CASL2TopSort.genEitherAxiom: No PRED_NAME for \""
              ++ shows s "\" found!") $ lkupPredName ssMap s
          genDisj qons = Disjunction (map genPred qons) nullRange
          genPred qon =
              genPredication (lPredName $ argSort qon) [mkXVarDecl qon]

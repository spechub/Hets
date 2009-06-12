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
import CASL.Utils
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
        sigTarg <-  trSig $ mtarget mor
        return mor
          { msource = sigSour
          , mtarget = sigTarg }
    map_sentence CASL2TopSort = transSen
    map_symbol CASL2TopSort _ = Set.singleton . id
    has_model_expansion CASL2TopSort = True

data PredInfo = PredInfo { topSort_PI    :: SORT
                         , directSuperSorts_PI :: Set.Set SORT
                         , predicate_PI  :: PRED_NAME
                         } deriving (Show, Ord, Eq)

type SubSortMap = Map.Map SORT PredInfo

generateSubSortMap :: Rel.Rel SORT
                   -> Map.Map Id (Set.Set PredType)
                   -> Result SubSortMap
generateSubSortMap sortRels pMap =
    let disAmbMap m  = Map.map disAmbPred m
        disAmbPred v = if (predicate_PI v) `Map.member` pMap
                       then disAmbPred' (1::Int) v'
                       else v
            where v' = add "_s" v
                  disAmbPred' x v1 =
                      if (predicate_PI v1) `Map.member` pMap
                      then disAmbPred' (x+1) (add (show x) v')
                      else v1
                  add s v1 = v1 {predicate_PI =
                                   case predicate_PI v1 of
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
            in PredInfo { topSort_PI = ts
                        , directSuperSorts_PI = Set.difference e mR
                        , predicate_PI = k }
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
transSig sig
    | Rel.null (sortRel sig) = hint (sig, [])
        "CASL2TopSort.transSig: Signature is unchanged (no subsorting present)"
        nullRange
    | otherwise = do
    subSortMap <- generateSubSortMap (sortRel sig) (predMap sig)
    let (dias2, newPredMap) = Map.mapAccum ( \ ds (un, ds1) -> (ds ++ ds1, un))
          [] $ Map.unionWithKey repError (transPredMap subSortMap
                  $ predMap sig) $ newPreds subSortMap
    Result dias2 $ Just ()
    axs <- generateAxioms subSortMap (predMap sig) (opMap sig)
    return (sig
        { sortSet = Set.fromList (map topSort_PI $ Map.elems subSortMap)
              `Set.union` (sortSet sig `Set.difference` Map.keysSet subSortMap)
        , sortRel = Rel.empty
        , opMap   = transOpMap subSortMap (opMap sig)
        , assocOps= transOpMap subSortMap (assocOps sig)
        , predMap = newPredMap
        }, axs ++ symmetryAxioms subSortMap (sortRel sig))
    where
          repError k (v1, d1) (v2, d2) =
              (Set.union v1 v2,
               Diag Warning
                     ("CASL2TopSort.transSig: generating " ++
                      "overloading: Predicate " ++ show k ++
                      " gets additional type(s): " ++ show v2) nullRange
               : d1 ++ d2 )
          newPreds mp =
              foldr (\ pI nm -> Map.insert (predicate_PI pI)
                                           (Set.singleton
                                            (PredType [topSort_PI pI]),[]) nm)
                    Map.empty (Map.elems mp)

transPredMap :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType)
             -> Map.Map PRED_NAME (Set.Set PredType, [Diagnosis])
transPredMap subSortMap = Map.map ( \ s -> (Set.map transType s, []))
    where transType t = t
            { predArgs = map ( \ s -> maybe s topSort_PI
                             $ Map.lookup s subSortMap) $ predArgs t }

transOpMap :: SubSortMap -> Map.Map OP_NAME (Set.Set OpType)
           -> Map.Map OP_NAME (Set.Set OpType)
transOpMap subSortMap = Map.map (tidySet . Set.map transType)
    where tidySet s = Set.fold joinPartial s s
            where joinPartial t@(OpType {opKind = Partial})
                      | t {opKind = Total} `Set.member` s = Set.delete t
                      | otherwise                         = id
                  joinPartial _ = id
          transType t =
              t { opArgs = map lkp (opArgs t)
                , opRes = lkp (opRes t)}
          lkp = (\s -> maybe s topSort_PI (Map.lookup s subSortMap))

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

symmetryAxioms :: SubSortMap -> Rel.Rel SORT -> [Named (FORMULA ())]
symmetryAxioms ssMap sortRels =
    let symSets = Rel.sccOfClosure sortRels
        mR = Rel.mostRight sortRels
        symTopSorts symSet = not (Set.null (Set.intersection mR symSet))
        xVar = mkSimpleId "x"
        updateLabel ts symS [sen] =
          reName ( \ s -> show ts ++ s ++ show symS) sen
        updateLabel _ _ _ = error "CASL2TopSort.symmetryAxioms"
        toAxioms symSet =
            [updateLabel ts symS (inlineAxioms CASL
                    "sort ts pred symS:ts\n\
                    \forall xVar : ts\n\
                    \. symS(xVar) %(_symmetric_with_)%")
                        | s<-(Set.toList(Set.difference symSet mR)),
                          let ts = lkupTop ssMap s,
                          let symS = fromJust (lkupPRED_NAME ssMap s)]

    in concatMap toAxioms (filter symTopSorts symSets)

generateAxioms :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType)
               -> Map.Map OP_NAME (Set.Set OpType)
               -> Result [Named (FORMULA ())]
generateAxioms subSortMap pMap oMap = do
    -- generate argument restrictions for operations
    axs <- Map.foldWithKey (procOpMapping subSortMap) (return []) oMap
    return $ reverse hi_axs ++ reverse p_axs ++ reverse axs
    where p_axs =
          -- generate argument restrictions for predicates
           Map.foldWithKey (\ pName set al ->
              al ++ Map.foldWithKey
                             ( \ sl -> genArgRest
                                      (genSenName "p" pName $ length sl)
                                      (genPredication pName)
                                      sl)
                                    [] (mkProfMapPred subSortMap set))
                   [] pMap
          hi_axs =
          -- generate subclass_of axioms derived from subsorts
          -- and non-emptyness axioms
              Map.fold (\ prdInf al ->
               let ts = topSort_PI prdInf
                   subS = predicate_PI prdInf
                   set = directSuperSorts_PI prdInf
                   supPreds =
                     map (\ s ->
                            maybe (error ("CASL2TopSort: genAxioms:" ++
                                   " impossible happend: " ++ show s))
                                  predicate_PI $ Map.lookup s subSortMap)
                         $ Set.toList set
                   x = mkSimpleId "x"
                in al ++ zipWith ( \ sen supS ->
                                      reName ( \ s -> show subS ++ s
                                                      ++ show supS) sen)
                         (concat [inlineAxioms CASL
                                  "sort ts\n\
                                  \pred subS,supS: ts\n\
                                  \ forall x : ts . subS(x) =>\n\
                                  \ supS(x) %(_subclassOf_)%"|supS<-supPreds]
                         ) supPreds ++
                         map ( \ sen -> reName (show subS ++) sen)
                                 (concat [inlineAxioms CASL
                                  "sort ts\n\
                                  \pred subS: ts \n\
                                  \. exists x:ts . \n\
                                  \ subS(x) %(_non_empty)%"])
             ) [] subSortMap

mkProfMapPred :: SubSortMap -> Set.Set PredType
              -> Map.Map [SORT] (Set.Set [Maybe PRED_NAME])
mkProfMapPred ssm = Set.fold seperate Map.empty
    where seperate pt = Rel.setInsert (pt2topSorts pt) (pt2preds pt)
          pt2topSorts = map (lkupTop ssm) . predArgs
          pt2preds = map (lkupPRED_NAME ssm) . predArgs

mkProfMapOp :: OP_NAME -> SubSortMap -> Set.Set OpType
              -> Result (Map.Map [SORT] (OpKind, Set.Set [Maybe PRED_NAME]))
mkProfMapOp opName ssm = Set.fold seperate (return Map.empty)
    where seperate ot r = do
              mp <- r
              Result dias' $ Just ()
              return $ Map.insertWith ( \ (k1, s1) (k2, s2) ->
                                           (min k1 k2, Set.union s1 s2))
                (pt2topSorts joinedList)
                (fKind, Set.singleton $ pt2preds joinedList) mp
              where joinedList = opArgs ot ++ [opRes ot]
                    fKind = opKind ot
                    dias' = if fKind == Partial
                             then [Diag Warning
                                        ("Please, check if operation \"" ++
                                         show opName ++
                                         "\" is still partial as intended,\
                                          \ since a joining of types could\
                                         \ have made it total!!")
                                        nullRange]
                             else []
          pt2topSorts = map (lkupTop ssm)
          pt2preds = map (lkupPRED_NAME ssm)

lkupTop :: SubSortMap -> SORT -> SORT
lkupTop ssm s = maybe s topSort_PI (Map.lookup s ssm)

lkupPRED_NAME :: SubSortMap -> SORT -> Maybe PRED_NAME
lkupPRED_NAME ssm s = maybe Nothing (Just . predicate_PI) (Map.lookup s ssm)

genArgRest :: String
           -> ([SORT] -> [TERM f] -> FORMULA f)
               -- ^ generates from a list of variables
               -- either the predication or function equation
           -> [SORT] -> (Set.Set [Maybe PRED_NAME])
           -> [Named (FORMULA f)] -> [Named (FORMULA f)]
genArgRest sen_name genProp sl spl fs =
    let vars = genVars sl
        mquant = genQuantification (genProp sl $ map toSortTerm vars) vars spl
    in maybe fs ( \ quant -> mapNamed (const quant) (makeNamed "" sen_name)
                             : fs) mquant

-- | generate a predication with qualified pred name
genPredication :: PRED_NAME -> [SORT] -> [TERM f] -> FORMULA f
genPredication pName sl ts = Predication (Qual_pred_name pName
   (Pred_type sl nullRange) nullRange) ts nullRange

genOpEquation :: OpKind -> OP_NAME -> [SORT] -> [TERM f] -> FORMULA f
genOpEquation kind opName sl terms =
    Strong_equation sortedOpTerm resTerm nullRange
    where sortedOpTerm = Sorted_term (Application (Qual_op_name opName
              opType nullRange) argTerms nullRange) resSort nullRange
          opType = Op_type kind argSorts resSort nullRange
          argTerms = init terms
          resTerm  = last terms
          argSorts = init sl
          resSort  = last sl

genVars :: [SORT] -> [TERM f]
genVars = zipWith toVarTerm varSymbs
    where varSymbs = map mkSimpleId
            (map (: []) "xyzuwv" ++ map ( \ i -> 'v' : show i) [(1::Int)..])

genSenName :: Show a => String -> a -> Int -> String
genSenName suff symbName arity =
    "arg_rest_" ++ show symbName ++ '_' : suff ++ '_' : show arity

genQuantification :: FORMULA f -- ^ either the predication or
                               -- function equation
                  -> [TERM f] -- ^ Qual_vars
                  -> (Set.Set [Maybe PRED_NAME])
                  -> Maybe (FORMULA f)
genQuantification prop vars spl = do
     dis <- genDisjunction vars spl
     return $ Quantification Universal vds
                (Implication prop dis True nullRange) nullRange
   where vds = reverse (foldl toVarDecl [] vars)
         toVarDecl :: [VAR_DECL] -> TERM f -> [VAR_DECL]
         toVarDecl [] (Qual_var n s _) = [Var_decl [n] s nullRange]
         toVarDecl xxs@(Var_decl l s1 _ : xs) (Qual_var n s _)
             | s1 == s = Var_decl (l ++ [n]) s1 nullRange:xs
             | otherwise = Var_decl [n] s nullRange : xxs
         toVarDecl _ _ =
             error "CASL2TopSort.toVarDecl: can only handle Qual_var"

genDisjunction :: [TERM f] -- ^ Qual_vars
                  -> (Set.Set [Maybe PRED_NAME])
                  -> Maybe (FORMULA f)
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
                | otherwise  = (Conjunction (reverse conjs) nullRange):acc
                where conjs = foldl genPred [] (zip vars pns)
            genPred acc (v@(Qual_var _ s _), mpn) =
                maybe acc (\ pn -> genPredication pn [s] [v]:acc) mpn
            genPred _ _ =
                error "CASL2TopSort.genPred: can only handle Qual_var"

-- | Each membership test of a subsort is transformed to a predication
-- of the corresponding unary predicate. Variables quantified over a
-- subsort yield a premise to the quantified formula that the
-- corresponding predicate holds. All typings are adjusted according
-- to the subsortmap and sort generation constraints are translated to
-- disjointness axioms.

transSen :: (Show f) => Sign f e -> FORMULA f -> Result (FORMULA f)
transSen sig f
    | Rel.null (sortRel sig) =
        Result [Diag Hint (
        "CASL2TopSort.transSen: Sentence is unchanged (no subsorting present)"
                             ) nullRange] (Just f)
    | otherwise = do
    ssm <- generateSubSortMap (sortRel sig)(predMap sig)
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
                 (\pn -> genPredication pn [lkupTop subSortMap s]
                                           [t'])
                 (lkupPRED_NAME subSortMap s)
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
              else Implication (mkVarPreds vdl) f1 True nullRange
          -- existential or unique-existential? then use conjuction
          relativize _ vdl f1 =
              if null vdl then f1
              else Conjunction [mkVarPreds vdl,f1] nullRange
          mkVarPreds [v] = mkVarPred v
          mkVarPreds vdl = Conjunction (map mkVarPred vdl) nullRange
          mkVarPred (Var_decl [v] s _) = mkVarPred1 s v
          mkVarPred (Var_decl vs s _) =
              Conjunction (map (mkVarPred1 s) vs) nullRange
          mkVarPred1 s v =
              let sTop = lkupTop subSortMap s
                  p = lkupPRED_NAME subSortMap s
              in case p of
                 -- no subsort? then no relativization
                 Nothing -> True_atom nullRange
                 Just p1 -> genPredication p1 [sTop] [Qual_var v s nullRange]



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
    _ ->
        error "CASL2TopSort.mapTerm"
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
            let (injOps,constrs) = partition isInjOp osl
                groupedInjOps = groupBy sameTarget $ sortBy compTarget injOps
            in if null constrs
               then case groupedInjOps of
                    [] -> fatal_error "No injective operation found" nullRange
                    [xs@(x : _)] -> return $ genQuant x $ genImpl xs
                    ((x : _) : _) -> return $ genQuant x
                        $ Conjunction (map genImpl groupedInjOps) nullRange
                    _ -> error "CASL2TopSort.genEitherAxiom.groupedInjOps"
               else Result [Diag Error
                                 ("CASL2TopSort: Cannot handle \
                                  \datatype constructors; only subsort \
                                  \embeddings are allowed with free and \
                                  \generated types!") nullRange] Nothing
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
          varName = mkSimpleId "x"
          mkVarTerm qon =
              Sorted_term (Qual_var varName s nullRange) s nullRange
              where s = lTop $ resultSort qon
          mkVarDecl qon =
              Var_decl [varName] (lTop (resultSort qon)) nullRange
          genQuant qon f = Quantification Universal [mkVarDecl qon] f nullRange
          genImpl []       = error "No OP_SYMB found"
          genImpl xs@(x:_) =
              assert (lTop (resultSort x) == lTop (argSort x))
              (if (resultSort x) == lTop (resultSort x)
               then genDisj xs
               else Implication (genProp x) (genDisj xs) True nullRange)
          genProp qon = genPredication (lPredName (resultSort qon))
                                       [lTop (resultSort qon)]
                                       [mkVarTerm qon]
          lPredName s = maybe (error $
              "CASL2TopSort.genEitherAxiom: No PRED_NAME for \""
              ++ shows s "\" found!") id $ lkupPRED_NAME ssMap s
          genDisj qons = Disjunction (map genPred qons) nullRange
          genPred qon = genPredication (lPredName $ argSort qon)
              [lTop $ resultSort qon] [mkVarTerm qon]

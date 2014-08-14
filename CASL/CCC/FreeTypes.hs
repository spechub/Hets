{- |
Module      :  $Header$
Description :  consistency checking of free types
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Consistency checking of free types
-}

module CASL.CCC.FreeTypes (checkFreeType) where

import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sign
import CASL.Simplify
import CASL.SimplifySen
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof (terminationProof)
import CASL.Overload (leqF, leqP)
import CASL.ToDoc

import Common.AS_Annotation
import Common.Consistency (Conservativity (..))
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils (nubOrd, number)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import Control.Monad

import Data.Function
import Data.List
import Data.Maybe

import qualified Data.Set as Set

-- | check values of constructors (free types have only total ones)
inhabited :: Set.Set SORT -> [OP_SYMB] -> Set.Set SORT
inhabited sorts cons = iterateInhabited sorts where
  argsRes = foldr (\ os -> case os of
    Qual_op_name _ (Op_type Total args res _) _ -> ((args, res) :)
    _ -> id) [] cons
  iterateInhabited l =
    if changed then iterateInhabited newL else newL where
      (newL, changed) = foldr (\ (ags, rs) p@(l', _) ->
        if all (`Set.member` l') ags && not (Set.member rs l')
        then (Set.insert rs l', True) else p) (l, False) argsRes

-- | just filter out the axioms generated for free types
isUserOrSortGen :: Named (FORMULA f) -> Bool
isUserOrSortGen ax = case stripPrefix "ga_" $ senAttr ax of
  Nothing -> True
  Just rname -> all (not . (`isPrefixOf` rname))
    ["disjoint_", "injective_", "selector_"]

getFs :: [Named (FORMULA f)] -> [FORMULA f]
getFs = map sentence . filter isUserOrSortGen

getExAxioms :: [Named (FORMULA f)] -> [FORMULA f]
getExAxioms = filter isExQuanti . getFs

getAxioms :: [Named (FORMULA f)] -> [FORMULA f]
getAxioms =
  filter (\ f -> not $ isSortGen f || isMembership f || isExQuanti f) . getFs

getInfoSubsort :: Morphism f e m -> [Named (FORMULA f)] -> [FORMULA f]
getInfoSubsort m = concatMap (infoSubsort esorts) . filter isMembership . getFs
  where esorts = Set.toList . emptySortSet $ mtarget m

getAxGroup :: GetRange f => Sign f e -> [Named (FORMULA f)] -> [[FORMULA f]]
getAxGroup sig = groupAxioms sig . filter (not . isDomain) . getAxioms

-- | get the constraints from sort generation axioms
constraintOfAxiom :: [FORMULA f] -> [[Constraint]]
constraintOfAxiom = foldr (\ f -> case f of
  Sort_gen_ax constrs _ -> (constrs :)
  _ -> id) []

recoverSortsAndConstructors :: [Named (FORMULA f)] -> [Named (FORMULA f)]
  -> (Set.Set SORT, [OP_SYMB])
recoverSortsAndConstructors osens fsn = let
  (srts, cons, _) = unzip3 . map recover_Sort_gen_ax
    . constraintOfAxiom . getFs $ osens ++ fsn
  in (Set.unions $ map Set.fromList srts, nubOrd $ concat cons)

-- check that patterns do not overlap, if not, return proof obligation.
getOverlapQuery :: (Ord f, GetRange f) => Sign f e -> [Named (FORMULA f)]
  -> [FORMULA f]
getOverlapQuery sig fsn = filter (not . is_True_atom) overlap_query where
        axPairs = concatMap pairs $ getAxGroup sig fsn
        olPairs = filter (\ (a, b) -> checkPatterns sig
                           (patternsOfAxiom a, patternsOfAxiom b)) axPairs
        subst (f1, f2) = ((f1, reverse sb1), (f2, reverse sb2))
          where (sb1, sb2) = st ((patternsOfAxiom f1, []),
                                 (patternsOfAxiom f2, []))
                st ((pa1, s1), (pa2, s2)) = case (pa1, pa2) of
                  (hd1 : tl1, hd2 : tl2)
                    | hd1 == hd2 -> st ((tl1, s1), (tl2, s2))
                    | isVar hd1 -> st ((tl1, (hd2, hd1) : s1), (tl2, s2))
                    | isVar hd2 -> st ((tl1, s1), (tl2, (hd1, hd2) : s2))
                    | otherwise -> st ((arguOfTerm hd1 ++ tl1, s1),
                                       (arguOfTerm hd2 ++ tl2, s2))
                  _ -> (s1, s2)
        quant f = mkForall (varDeclOfF f) f
        overlap_query = map (quant . simplifyFormula id . overlapQuery . subst)
          olPairs
{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getDefsForOld :: GetRange f => Morphism f e m -> [Named (FORMULA f)]
  -> [FORMULA f]
getDefsForOld m fsn = let
        sig = imageOfMorphism m
        oldOpMap = opMap sig
        oldPredMap = predMap sig
        axioms = getAxioms fsn
    in foldr (\ f -> case leadingSym f of
         Just (Left (Qual_op_name ident ot _))
           | MapSet.member ident (toOpType ot) oldOpMap -> (f :)
         Just (Right (Qual_pred_name ident pt _))
           | MapSet.member ident (toPredType pt) oldPredMap -> (f :)
         _ -> id) [] axioms

{- | newly introduced sorts
(the input signature is the domain of the inclusion morphism) -}
getNSorts :: Sign f e -> Morphism f e m -> Set.Set SORT
getNSorts osig m = on Set.difference sortSet (mtarget m) osig

-- | all only generated sorts
getNotFreeSorts :: Set.Set SORT -> [Named (FORMULA f)] -> Set.Set SORT
getNotFreeSorts nSorts fsn = Set.intersection nSorts
    $ Set.difference (getGenSorts fsn) freeSorts where
        freeSorts = foldr (\ f -> case sentence f of
          Sort_gen_ax csts True -> Set.union . Set.fromList $ map newSort csts
          _ -> id) Set.empty fsn

getGenSorts :: [Named (FORMULA f)] -> Set.Set SORT
getGenSorts = fst . recoverSortsAndConstructors []

-- | non-inhabited non-empty sorts
getNefsorts :: (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
    -> Set.Set SORT -> [Named (FORMULA f)] -> Set.Set SORT
getNefsorts (osig, osens) m nSorts fsn =
  Set.difference fsorts $ inhabited oldSorts cons where
    oldSorts = sortSet osig
    esorts = emptySortSet $ mtarget m
    (srts, cons) = recoverSortsAndConstructors osens fsn
    fsorts = Set.difference (Set.intersection nSorts srts) esorts

getDataStatus :: GetRange f
  => (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
  -> [Named (FORMULA f)] -> Conservativity
getDataStatus (osig, osens) m fsn = dataStatus where
        tsig = mtarget m
        subs = Rel.keysSet . Rel.rmNullSets $ sortRel tsig
        nSorts = getNSorts osig m
        gens = Set.intersection nSorts . fst
          $ recoverSortsAndConstructors osens fsn
        dataStatus
          | Set.null nSorts = Def
          | not $ Set.null $ Set.difference (Set.difference nSorts gens) subs
              = Cons
          | otherwise = Mono

getOpsPredsAndExAxioms :: GetRange f
  => Morphism f e m -> [Named (FORMULA f)] -> [FORMULA f]
getOpsPredsAndExAxioms m fsn = getDefsForOld m fsn ++ getExAxioms fsn

getConStatus :: (GetRange f, Ord f)
  => (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
  -> [Named (FORMULA f)] -> Conservativity
getConStatus oTh m fsn = min dataStatus defStatus where
  dataStatus = getDataStatus oTh m fsn
  defStatus = if null $ getOpsPredsAndExAxioms m fsn
    then Def else Cons

getObligations :: (GetRange f, Ord f)
  => Morphism f e m -> [Named (FORMULA f)] -> [FORMULA f]
getObligations m fsn = getOpsPredsAndExAxioms m fsn
  ++ getInfoSubsort m fsn ++ getOverlapQuery (mtarget m) fsn

-- | check whether it is the domain of a partial function
isDomain :: FORMULA f -> Bool
isDomain f = case quanti f of
  Relation (Definedness _ _) Equivalence f' _ -> not (containDef f')
  Definedness _ _ -> True
  _ -> False

isDomainDef :: FORMULA f -> Bool
isDomainDef f = isJust (domainDef f) && isDomain f

domainDef :: FORMULA f -> Maybe (TERM f, FORMULA f)
domainDef f = case quanti f of
  Relation (Definedness t _) Equivalence f' _ -> Just (t, f')
  _ -> Nothing

-- | extract the domain-list of partial functions
domainList :: [FORMULA f] -> [(TERM f, FORMULA f)]
domainList = mapMaybe domainDef

-- | check whether it contains a definedness formula in correct form
correctDef :: FORMULA f -> Bool
correctDef f = case quanti f of
  Relation (Definedness _ _) c _ _ | c /= Equivalence -> True
  Negation (Definedness _ _) _ -> True
  Definedness _ _ -> True
  _ -> False

-- check the definitional form of the partial axioms
checkDefinitional :: (FormExtension f, TermExtension f)
  => Sign f e -> [Named (FORMULA f)]
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkDefinitional tsig fsn = let
       formatAxiom = flip showDoc "" . simplifyCASLSen tsig
       (noLSyms, withLSyms) = partition (isNothing . fst . snd)
         $ map (\ a -> (a, leadingSymPos a)) $ getAxioms fsn
       partialLSyms = foldr (\ (a, (ma, _)) -> case ma of
         Just (Left (Application t@(Qual_op_name _ (Op_type k _ _ _) _) _ _))
           | k == Partial -> ((a, t) :)
         _ -> id) [] withLSyms
       (domainDefs, otherPartials) = partition (isDomainDef . fst) partialLSyms
       (withDefs, withOutDefs) = partition (containDef . fst) otherPartials
       (correctDefs, wrongDefs) = partition (correctDef . fst) withDefs
       grDomainDefs = groupBy (on (==) snd) $ sortBy (on compare snd) domainDefs
       (multDomainDefs, oneDomainDefs) = partition (\ l -> case l of
          [_] -> False
          _ -> True) grDomainDefs
       singleDomainDefs = map head oneDomainDefs
       nonCompleteDomainDefs = filter (\ (da, _) -> case domainDef da of
         Just (ta, _) | all isVar $ arguOfTerm ta -> False
         _ -> True) singleDomainDefs
       domainObls = concatMap (\ (da, dt) -> map (\ (de, _) -> (da, de))
           $ filter ((== dt) . snd) correctDefs) singleDomainDefs
       nonEqDoms = filter (\ (da, de) ->
         case (domainDef da, quanti de) of
           (Just (ta, _), Relation (Definedness te _) c _ _)
             | c /= Equivalence && sameOpsApp tsig ta te ->
             case leadingTermPredication de of
               Just (Left t) | eqPattern tsig te t -> False
               _ -> True
           _ -> True) domainObls
       defOpSymbs = Set.fromList $ map (snd . head) grDomainDefs
         ++ map snd correctDefs
       wrongWithoutDefs = filter ((`Set.notMember` defOpSymbs) . snd)
         withOutDefs
       ds = map (\ (a, (_, pos)) -> Diag
         Warning ("missing leading symbol in:\n" ++ formatAxiom a) pos) noLSyms
         ++ map (\ (a, t) -> Diag
         Warning ("definedness is not definitional:\n" ++ formatAxiom a)
                $ getRange t) wrongDefs
         ++ map (\ l@((_, t) : _) -> Diag Warning (unlines $
             ("multiple definedness definitions for: " ++ showDoc t "")
             : map (formatAxiom . fst) l) $ getRange t) multDomainDefs
         ++ map (\ (a, t) -> Diag
         Warning ("missing definedness condition for partial '"
                      ++ showDoc t "' in\n" ++ formatAxiom a)
             $ getRange t) wrongWithoutDefs
         ++ map (\ (da, _) -> Diag
         Warning ("non-complete domain axiom: " ++ formatAxiom da)
             $ getRange da) nonCompleteDomainDefs
         ++ map (\ (_, de) -> Diag
         Warning ("unexpected domain condition for partial definition: "
                  ++ formatAxiom de)
             $ getRange de) nonEqDoms
       in if null ds then Nothing else Just $ Result ds Nothing

{-
  call the symbols in the image of the signature morphism "new"

- each new sort must be a free type,
  i.e. it must occur in a sort generation constraint that is marked as free
    (Sort_gen_ax constrs True)
    such that the sort is in srts,
        where (srts,ops,_)=recover_Sort_gen_ax constrs
    if not, output "don't know"
  and there must be one term of that sort (inhabited)
    if not, output "no"
- group the axioms according to their leading operation/predicate symbol,
  i.e. the f resp. the p in
  forall x_1:s_n .... x_n:s_n .                  f(t_1,...,t_m)=t
  forall x_1:s_n .... x_n:s_n .       phi =>      f(t_1,...,t_m)=t
                                  Implication  Application  Strong_equation
  forall x_1:s_n .... x_n:s_n .                  p(t_1,...,t_m)<=>phi
  forall x_1:s_n .... x_n:s_n .    phi1  =>      p(t_1,...,t_m)<=>phi
                                 Implication   Predication    Equivalence
  if there are axioms not being of this form, output "don't know"
-}
checkSort :: (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
    -> [Named (FORMULA f)]
    -> Maybe (Result (Conservativity, [FORMULA f]))
checkSort oTh@(osig, _) m fsn
    | null fsn && Set.null nSorts =
        let sSig = imageOfMorphism m
            tSig = mtarget m
            cond = MapSet.null (diffOpMapSet (opMap tSig) $ opMap sSig)
              && MapSet.null (diffMapSet (predMap tSig) $ predMap sSig)
        in Just $ justHint (if cond then Def else Cons, [])
        $ (if cond then "neither symbols"
          else "neither sorts") ++ " nor sentences have been added"
    | not $ Set.null notFreeSorts =
        mkUnknown "some types are not freely generated" notFreeSorts
    | not $ Set.null nefsorts = mkWarn "some sorts are not inhabited"
        nefsorts (Inconsistent, [])
    | not $ Set.null genNotNew = mkUnknown "some free types are not new"
        genNotNew
    | otherwise = Nothing
    where
        nSorts = getNSorts osig m
        notFreeSorts = getNotFreeSorts nSorts fsn
        nefsorts = getNefsorts oTh m nSorts fsn
        genNotNew = Set.difference (getGenSorts fsn) nSorts
        mkWarn s i r = Just $ Result [mkDiag Warning s i] $ Just r
        mkUnknown s i = mkWarn s i (Unknown s, [])

checkLeadingTerms :: (FormExtension f, TermExtension f, Ord f)
  => [Named (FORMULA f)] -> Morphism f e m -> [Named (FORMULA f)]
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkLeadingTerms osens m fsn = let
    tsig = mtarget m
    constructors = snd $ recoverSortsAndConstructors osens fsn
    ltp = mapMaybe leadingTermPredication $ getAxioms fsn
    formatTerm = flip showDoc "" . simplifyCASLTerm tsig
    args = foldr (\ ei -> case ei of
      Left (Application os ts qs) ->
         ((qs, "term for " ++ show (opSymbName os), ts) :)
      Right (Predication ps ts qs) ->
         ((qs, "predicate " ++ show (predSymbName ps), ts) :)
      _ -> id) [] ltp
    ds = foldr (\ (qs, d, ts) l ->
           let vs = concatMap varOfTerm ts
               dupVs = vs \\ Set.toList (Set.fromList vs)
               nonCs = checkTerms tsig constructors ts
               td = " in leading " ++ d ++ ": "
           in map (\ v -> Diag Warning
                    ("duplicate variable" ++ td ++ formatTerm v) qs) dupVs
              ++ map (\ t -> Diag Warning
                     ("non-constructor" ++ td ++ formatTerm t)
                     qs) nonCs
              ++ l) [] args
    in if null ds then Nothing else Just $ Result ds Nothing

-- check the sufficient completeness
checkIncomplete :: (FormExtension f, TermExtension f, Ord f)
  => [Named (FORMULA f)] -> Morphism f e m
  -> [Named (FORMULA f)]
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkIncomplete osens m fsn = case getNotComplete osens m fsn of
  [] -> Nothing
  incomplete -> let obligations = getObligations m fsn in Just $ Result
      (map (\ (ds, fs@(hd : _)) -> let
        (lSym, pos) = leadingSymPos hd
        sname = case fmap extractLeadingSymb lSym of
                      Just (Left opS) -> opSymbName opS
                      Just (Right pS) -> predSymbName pS
                      _ -> error "CASL.CCC.FreeTypes.<Symb_Name>"
        in Diag Warning (intercalate "\n" $
             ("the definition of " ++ show sname ++ " is not complete")
             : "the defining formula group is:"
             : map (\ (f, n) -> "  " ++ shows n ". "
                    ++ showDoc (simplifyCASLSen (mtarget m) f) "") (number fs)
             ++ map diagString ds) pos)
       incomplete) $ Just (Cons, obligations)

checkTerminal :: (FormExtension f, GetRange f, Ord f)
  => (Sign f e, [Named (FORMULA f)]) -> Morphism f e m -> [Named (FORMULA f)]
  -> IO (Maybe (Result (Conservativity, [FORMULA f])))
checkTerminal oTh m fsn = do
    let fs = getFs fsn
        fs_terminalProof = filter (\ f ->
          not $ isSortGen f || isMembership f || isExQuanti f || isDomain f
          ) fs
        domains = domainList fs
        obligations = getObligations m fsn
        conStatus = getConStatus oTh m fsn
        res = if null obligations then Nothing else
                  Just $ return (conStatus, obligations)
    (proof, str) <- terminationProof (mtarget m) fs_terminalProof domains
    return $ case proof of
        Just True -> res
        _ -> Just $ warning (Cons, obligations)
             (if isJust proof then "not terminating"
              else "cannot prove termination: " ++ str) nullRange

checkPositive :: [Named (FORMULA f)] -> [Named (FORMULA f)] -> Bool
checkPositive osens fsn = all checkPos $ map sentence $ osens ++ fsn

checkPos :: FORMULA f -> Bool
checkPos f = case quanti f of
      Junction _ cs _ -> all checkPos cs
      Relation i1 c i2 _ -> let
        c1 = checkPos i1
        c2 = checkPos i2
        in if c == Equivalence then c1 == c2 else c1 <= c2
      Negation n _ -> not $ checkPos n
      Atom b _ -> b
      Predication {} -> True
      Definedness {} -> True
      Equation {} -> True
      Sort_gen_ax {} -> True -- ignore
      _ -> False

{- -----------------------------------------------------------------------
   function checkFreeType:
   - check if leading symbols are new (not in the image of morphism),
           if not, return them as obligations
   - generated datatype is free
   - if new sort is not etype or esort, it can not be empty.
   - the leading terms consist of variables and constructors only,
           if not, return Nothing
     - split function leading_Symb into
       leadingTermPredication
       and
       extractLeadingSymb
     - collect all operation symbols from recover_Sort_gen_ax fconstrs
                                                       (= constructors)
   - no variable occurs twice in a leading term, if not, return Nothing
   - check that patterns do not overlap, if not, return obligations
     This means:
       in each group of the grouped axioms:
       all patterns of leading terms/formulas are disjoint
       this means: either leading symbol is a variable,
                           and there is just one axiom
                   otherwise, group axioms according to leading symbol
                              no symbol may be a variable
                              check recursively the arguments of
                              constructor in each group
  - sufficient completeness
  - termination proof
------------------------------------------------------------------------
free datatypes and recursive equations are consistent -}
checkFreeType :: (FormExtension f, TermExtension f, Ord f)
  => (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
  -> [Named (FORMULA f)] -> IO (Result (Conservativity, [FORMULA f]))
checkFreeType oTh@(_, osens) m axs = do
  ms <- mapM ($ axs)
    [ return . checkDefinitional (mtarget m)
    , return . checkSort oTh m
    , return . checkLeadingTerms osens m
    , return . checkIncomplete osens m
    , checkTerminal oTh m ]
  return $ case catMaybes ms of
    [] -> return (getConStatus oTh m axs, [])
    a : _ -> case a of
      Result _ Nothing -> if checkPositive osens axs then
        justHint (Cons, []) "theory is positive!"
        else a
      _ -> a

{- | group the axioms according to their leading symbol,
output Nothing if there is some axiom in incorrect form -}
groupAxioms :: GetRange f => Sign f e -> [FORMULA f] -> [[FORMULA f]]
groupAxioms sig phis = map (map snd)
   $ Rel.partList (\ (e1, _) (e2, _) -> case (e1, e2) of
       (Left (Qual_op_name o1 t1 _), Left (Qual_op_name o2 t2 _)) ->
           o1 == o2 && on (leqF sig) toOpType t1 t2
       (Right (Qual_pred_name p1 t1 _), Right (Qual_pred_name p2 t2 _)) ->
           p1 == p2 && on (leqP sig) toPredType t1 t2
       _ -> False)
   $ foldr (\ f -> case leadingSym f of
    Just ei -> ((ei, f) :)
    Nothing -> id) [] phis

-- | return the non-constructor terms of arguments of a leading term
checkTerms :: Sign f e -> [OP_SYMB] -> [TERM f] -> [TERM f]
checkTerms sig cons = concatMap checkT
  where checkT t = case unsortedTerm t of
          Qual_var {} -> []
          Application subop subts _ ->
            if isCons sig cons subop then concatMap checkT subts else [t]
          _ -> [t]

{- | check whether the operation symbol is a constructor
(or a related overloaded variant). -}
isCons :: Sign f e -> [OP_SYMB] -> OP_SYMB -> Bool
isCons s cons os = any (is_Cons os) cons
    where is_Cons (Qual_op_name on1 ot1 _) (Qual_op_name on2 ot2 _) =
            on1 == on2 && on (leqF s) toOpType ot1 ot2
          is_Cons _ _ = False

-- | create all possible pairs from a list
pairs :: [a] -> [(a, a)]
pairs ps = case ps of
  hd : tl@(_ : _) -> map (\ x -> (hd, x)) tl ++ pairs tl
  _ -> []

-- | get the patterns of a axiom
patternsOfAxiom :: FORMULA f -> [TERM f]
patternsOfAxiom = snd . topIdOfAxiom

topIdOfAxiom :: FORMULA f -> ((Id, Int), [TERM f])
topIdOfAxiom f = case quanti f of
    Negation f' _ -> topIdOfAxiom f'
    Relation _ c f' _ | c /= Equivalence -> topIdOfAxiom f'
    Relation f' Equivalence _ _ -> topIdOfAxiom f'
    Predication p ts _ -> ((predSymbName p, length ts), ts)
    Equation t _ _ _ -> topIdOfTerm t
    Definedness t _ -> topIdOfTerm t
    _ -> nullId

-- | check whether two patterns are overlapped
checkPatterns :: Eq f => Sign f e -> ([TERM f], [TERM f]) -> Bool
checkPatterns sig (ps1, ps2) = case (ps1, ps2) of
  (hd1 : tl1, hd2 : tl2) ->
      if isVar hd1 || isVar hd2 then checkPatterns sig (tl1, tl2)
      else sameOpsApp sig hd1 hd2 && checkPatterns sig
               (arguOfTerm hd1 ++ tl1, arguOfTerm hd2 ++ tl2)
  _ -> True

{- | get the axiom from left hand side of a implication,
if there is no implication, then return atomic formula true -}
conditionAxiom :: FORMULA f -> FORMULA f
conditionAxiom f = case quanti f of
                     Relation f' c _ _ | c /= Equivalence -> f'
                     _ -> trueForm

{- | get the axiom from right hand side of a equivalence,
if there is no equivalence, then return atomic formula true -}
resultAxiom :: FORMULA f -> FORMULA f
resultAxiom f = case quanti f of
                  Relation _ c f' _ | c /= Equivalence -> resultAxiom f'
                  Relation _ Equivalence f' _ -> f'
                  _ -> trueForm

{- | get the term from right hand side of a equation in a formula,
if there is no equation, then return a simple id -}
resultTerm :: FORMULA f -> TERM f
resultTerm f = case quanti f of
                 Relation _ c f' _ | c /= Equivalence -> resultTerm f'
                 Negation (Definedness _ _) _ ->
                   varOrConst (mkSimpleId "undefined")
                 Equation _ _ t _ -> t
                 _ -> varOrConst (mkSimpleId "unknown")

-- | create the proof obligation for a pair of overlapped formulas
overlapQuery :: (GetRange f, Eq f)
  => ((FORMULA f, [(TERM f, TERM f)]), (FORMULA f, [(TERM f, TERM f)]))
    -> FORMULA f
overlapQuery ((a1, s1), (a2, s2)) =
        case leadingSym a1 of
          Just (Left _)
            | containNeg a1 && not (containNeg a2) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg (Definedness resT2 nullRange))
            | containNeg a2 && not (containNeg a1) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg (Definedness resT1 nullRange))
            | containNeg a1 && containNeg a2 -> trueForm
            | otherwise ->
                mkImpl (conjunct [con1, con2])
                            (mkStEq resT1 resT2)
          Just (Right _)
            | containNeg a1 && not (containNeg a2) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg resA2)
            | containNeg a2 && not (containNeg a1) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg resA1)
            | containNeg a1 && containNeg a2 -> trueForm
            | otherwise ->
                mkImpl (conjunct [con1, con2])
                            (conjunct [resA1, resA2])
          _ -> error "CASL.CCC.FreeTypes.<overlapQuery>"
      where [c1, c2] = map conditionAxiom [a1, a2]
            [t1, t2] = map resultTerm [a1, a2]
            [r1, r2] = map resultAxiom [a1, a2]
            con1 = substiF s1 c1
            con2 = substiF s2 c2
            resT1 = substitute s1 t1
            resT2 = substitute s2 t2
            resA1 = substiF s1 r1
            resA2 = substiF s2 r2


getNotComplete :: (GetRange f, FormExtension f, TermExtension f)
  => [Named (FORMULA f)] -> Morphism f e m -> [Named (FORMULA f)]
  -> [([Diagnosis], [FORMULA f])]
getNotComplete osens m fsn =
  let constructors = snd $ recoverSortsAndConstructors osens fsn
      consMap = foldr (\ (Qual_op_name o ot _) ->
        MapSet.insert (res_OP_TYPE ot) (o, ot)) MapSet.empty constructors
      consMap2 = foldr (\ (Qual_op_name o ot _) ->
        MapSet.insert o ot) MapSet.empty constructors
      sig = mtarget m
  in
  filter (not . null . fst)
  $ map (\ g ->
         (diags $ let l = map topIdOfAxiom g in
                  case Set.toList . Set.fromList $ map fst l of
                    [(p, i)] -> completePatterns sig consMap consMap2
                      ([(showId p "", i)], map snd l)
                    l2 -> fail $ "wrongly grouped leading terms "
                      ++ show l2
         , g)) $ getAxGroup sig fsn

varToPat :: TERM f -> TERM f
varToPat t = case t of
  Sorted_term t' _ _ -> varToPat t'
  Cast t' _ _ -> varToPat t'
  Qual_var _ s r -> Qual_var (mkSimpleId "_") s r
  _ -> t

type LeadArgs = [(String, Int)]

getNextArg :: Bool -> String -> LeadArgs -> (Bool, String, LeadArgs)
getNextArg b p l = case l of
  [] -> (False, if b then p else "_", [])
  h : r -> case h of
    (i, c) -> if c == 0 then (b, i, r) else
      let (b1, sl, r2) = getNextN c b p r
      in (b1, i ++ "(" ++ intercalate ", " sl ++ ")", r2)

getNextN :: Int -> Bool -> String -> LeadArgs -> (Bool, [String], LeadArgs)
getNextN c b p l = if c <= 0 then (b, [], l) else
  let (b1, s, r) = getNextArg b p l
      (b2, sl, r2) = getNextN (c - 1) b1 p r
  in (b2, s : sl, r2)

showLeadingArgs :: String -> LeadArgs -> String
showLeadingArgs p l = let (_, r, _) = getNextArg True p $ reverse l in r

-- | check whether the patterns of a function or predicate are complete
completePatterns :: (FormExtension f, TermExtension f) => Sign f e
  -> MapSet.MapSet SORT (OP_NAME, OP_TYPE)
  -> MapSet.MapSet OP_NAME OP_TYPE -> (LeadArgs, [[TERM f]])
  -> Result ()
completePatterns tsig consMap consMap2 (leadingArgs, pas)
    | all null pas = return ()
    | any null pas = fail "wrongly grouped leading terms"
    | otherwise = let
          pa_group allCons = let
              p_g c@(_, l) p = (c : leadingArgs, map (\ (h : t) ->
                if isVar h
                then replicate l (varToPat h) ++ t
                else arguOfTerm h ++ t) p)
              in map (\ (c, ct) -> p_g (showId c "", length $ args_OP_TYPE ct)
                     $ filter (\ (h : _) -> case unsortedTerm h of
                           Application (Qual_op_name o ot _) _ _ ->
                             c == o && on (leqF tsig) toOpType ct ot
                           _ -> True) pas)
                 $ Set.toList allCons
          (hds, tls) = unzip $ map (\ (hd : tl) -> (hd, tl)) pas
          consAppls@(_ : _) = mapMaybe (\ t -> case unsortedTerm t of
            Application (Qual_op_name o ot _) _ _ ->
                Just (o, Set.filter (on (leqF tsig) toOpType ot)
                   $ MapSet.lookup o consMap2)
            _ -> Nothing) hds
          consSrt = foldr1 Set.intersection $ map (Set.map res_OP_TYPE . snd)
            consAppls
         in if all isVar hds
            then completePatterns tsig consMap consMap2
                     (("_", 0) : leadingArgs, tls)
            else case Set.toList consSrt of
                  [] -> fail $
                    "no common result type for constructors found: "
                       ++ showDoc consAppls ""
                  cSrt : _ -> do
                    let allCons = MapSet.lookup cSrt consMap
                        conpats = Set.fromList
                          $ concatMap (\ (o, cs)
                                       -> map (\ s -> (o, s)) $ Set.toList cs)
                          consAppls
                        missCons = Set.toList $ Set.difference allCons conpats
                    when (Set.null allCons) . fail
                      $ "no constructors for result type found: " ++ show cSrt
                    unless (null missCons || any isVar hds) . justWarn ()
                      $ "missing pattern"
                      ++ (if null $ tail missCons then "" else "s")
                      ++ " for: "
                      ++ intercalate "  \n"
                         (map (\ (o, ot) -> showLeadingArgs
                               (case args_OP_TYPE ot of
                                 [] -> showId o ""
                                 l -> showId o "("
                                   ++ intercalate "," (map (const "_") l)
                                   ++ ")")
                               leadingArgs) missCons)
                    mapM_ (completePatterns tsig consMap consMap2)
                              (pa_group allCons)

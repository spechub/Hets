{- |
Module      :  $Header$
Description :  consistency checking of free types
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mgross@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Consistency checking of free types
-}

module CASL.CCC.FreeTypes (checkFreeType) where

import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import CASL.Morphism
import CASL.Sign (OpType (..), PredType (..), Sign (..), sortSet, sortOfTerm)
import CASL.SimplifySen (simplifyCASLSen)
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof (terminationProof, opSymName, predSymName)

import Common.AS_Annotation
import Common.Consistency (Conservativity (..))
import Common.DocUtils (showDoc)
import Common.Id
import Common.Result (Result, warning)
import Common.Utils (nubOrd)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import Data.List
import Data.Maybe

import qualified Data.Set as Set

inhabited :: [SORT] -> [OP_SYMB] -> [SORT]
inhabited sorts cons = iterateInhabited sorts
    where argsRes = foldr (\ os -> case os of
                                 Op_name _ -> id
                                 Qual_op_name _ (Op_type _ args res _) _ ->
                                   ((args, res) :)) [] cons
          iterateInhabited l =
                    if l == newL then newL else iterateInhabited newL
                            where newL = foldr (\ (ags, rs) l' ->
                                                  if all (`elem` l') ags
                                                      && notElem rs l'
                                                  then rs : l'
                                                  else l') l argsRes

-- | just filter out the axioms generated for free types
isUserOrSortGen :: Named (FORMULA f) -> Bool
isUserOrSortGen ax = case stripPrefix "ga_" $ senAttr ax of
  Nothing -> True
  Just rname -> all (not . (`isPrefixOf` rname))
                ["disjoint_", "injective_", "selector_"]

getFs :: [Named (FORMULA f)] -> [FORMULA f]
getFs = map sentence . filter isUserOrSortGen

getExAxioms :: [Named (FORMULA ())] -> [FORMULA ()]
getExAxioms = filter isExQuanti . getFs

getAxioms :: [Named (FORMULA ())] -> [FORMULA ()]
getAxioms = filter (\ f ->
   not $ isSortGen f || isMembership f || isExQuanti f) . getFs

getInfoSubsort :: Morphism () () ()
    -> [Named (FORMULA ())] -> [FORMULA ()]
getInfoSubsort m fsn = info_subsort
    where
        fs = getFs fsn
        memberships = filter isMembership fs
        tsig = mtarget m
        esorts = Set.toList $ emptySortSet tsig
        info_subsort = concatMap (infoSubsort esorts) memberships

getAxGroup :: [Named (FORMULA ())]
    -> Maybe [(Either OP_SYMB PRED_SYMB, [FORMULA ()])]
getAxGroup fsn = axGroup
    where
        axioms = getAxioms fsn
        axioms' = map quanti axioms
        ax_without_dom = filter (not . isDomain) axioms'
        axGroup = groupAxioms ax_without_dom

-- | get the constraints from sort generation axioms
constraintOfAxiom :: [FORMULA f] -> [[Constraint]]
constraintOfAxiom = foldr (\ f -> case f of
      Sort_gen_ax constrs _ -> (constrs :)
      _ -> id) []

recoverSortsAndConstructors :: [Named (FORMULA f)] -> [Named (FORMULA f)]
  -> ([SORT], [OP_SYMB])
recoverSortsAndConstructors osens fsn = let
  (srts, cons, _) = unzip3 . map recover_Sort_gen_ax
    . constraintOfAxiom . getFs $ osens ++ fsn
  in (nubOrd $ concat srts, nubOrd $ concat cons)

getConstructors :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())] -> [OP_SYMB]
getConstructors osens m fsn = let tsig = mtarget m in
    constructorOverload tsig (opMap tsig)
          . snd $ recoverSortsAndConstructors osens fsn

-- check that patterns do not overlap, if not, return proof obligation.
getOverlapQuery :: [Named (FORMULA ())] -> [FORMULA ()]
getOverlapQuery fsn = overlap_query
    where
        axGroup = getAxGroup fsn
        axPairs =
            case axGroup of
              Just sym_fs -> concatMap (pairs . snd) sym_fs
              Nothing -> error "CASL.CCC.FreeTypes.<axPairs>"
        olPairs = filter (\ (a, b) -> checkPatterns
                           (patternsOfAxiom a, patternsOfAxiom b)) axPairs
        subst (f1, f2) = ((f1, reverse sb1), (f2, reverse sb2))
          where (sb1, sb2) = st ((patternsOfAxiom f1, []),
                                 (patternsOfAxiom f2, []))
                st ((pa1, s1), (pa2, s2)) = case (pa1, pa2) of
                  (hd1 : tl1, hd2 : tl2)
                    | hd1 == hd2 -> st ((tl1, s1), (tl2, s2))
                    | isVar hd1 -> st ((tl1, (hd2, hd1) : s1), (tl2, s2))
                    | isVar hd2 -> st ((tl1, s1), (tl2, (hd1, hd2) : s2))
                    | otherwise -> st ((patternsOfTerm hd1 ++ tl1, s1),
                                       (patternsOfTerm hd2 ++ tl2, s2))
                  _ -> (s1, s2)
        olPairsWithS = map subst olPairs
        overlap_qu = map overlapQuery olPairsWithS
        overlap_query = map (\ f -> Quantification Universal (varDeclOfF f) f
                                nullRange) overlap_qu
{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getOOps :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getOOps m fsn = let
        sig = imageOfMorphism m
        oldOpMap = opMap sig
        axioms = getAxioms fsn
        op_fs = filter (\ f -> case leadingSym f of
                               Just (Left _) -> True
                               _ -> False) axioms
        find_ot (ident, ot) = MapSet.member ident ot oldOpMap
    in filter (find_ot . head . filterOp . leadingSym) op_fs

{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getOPreds :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getOPreds m fsn =
    let sig = imageOfMorphism m
        oldPredMap = predMap sig
        axioms = getAxioms fsn
        pred_fs = filter (\ f -> case leadingSym f of
                                 Just (Right _) -> True
                                 _ -> False) axioms
        find_pt (ident, pt) = MapSet.member ident pt oldPredMap
    in filter (find_pt . head . filterPred . leadingSym) pred_fs

{- | newly introduced sorts
(the input signature is the domain of the inclusion morphism) -}
getNSorts :: Sign () () -> Morphism () () () -> [Id]
getNSorts osig m = Set.toList
  . Set.difference (sortSet $ mtarget m) $ sortSet osig

getNotFreeSorts :: Sign () () -> Morphism () () ()
    -> [Named (FORMULA ())] -> [SORT]
getNotFreeSorts osig m fsn = notFreeSorts
    where
        fs = getFs fsn
        axOfS = filter (\ f -> isSortGen f || isMembership f) fs
        nSorts = getNSorts osig m
        notFreeSorts = filter (\ s -> isFreeGenSort s axOfS == Just False)
                       nSorts

getNefsorts :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())] -> [SORT]
getNefsorts (osig, osens) m fsn = nefsorts
    where
        tsig = mtarget m
        oldSorts = sortSet osig
        oSorts = Set.toList oldSorts
        esorts = Set.toList $ emptySortSet tsig
        nSorts = getNSorts osig m
        (srts, cons) = recoverSortsAndConstructors osens fsn
        f_Inhabited = inhabited oSorts cons
        fsorts = filter (`notElem` esorts) $ intersect nSorts srts
        nefsorts = filter (`notElem` f_Inhabited) fsorts

getDataStatus :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())] -> Conservativity
getDataStatus (osig, osens) m fsn = dataStatus
    where
        tsig = mtarget m
        sR = Rel.toList $ sortRel tsig
        subs = map fst sR
        nSorts = getNSorts osig m
        gens = intersect nSorts . fst $ recoverSortsAndConstructors osens fsn
        dataStatus
          | null nSorts = Def
          | any (\ s -> notElem s subs && notElem s gens) nSorts = Cons
          | otherwise = Mono

getNotComplete :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())] -> [[FORMULA ()]]
getNotComplete osens m fsn = not_complete
    where
        constructors = getConstructors osens m fsn
        axGroup = getAxGroup fsn
        axGroups = case axGroup of
                       Just sym_fs -> map snd sym_fs
                       Nothing -> error "CASL.CCC.FreeTypes.<axGroups>"
        not_complete = filter (not . completePatterns constructors
                               . map patternsOfAxiom) axGroups

getOpsPredsAndExAxioms :: Morphism () () () -> [Named (FORMULA ())]
  -> [FORMULA ()]
getOpsPredsAndExAxioms m fsn =
  getOOps m fsn ++ getOPreds m fsn ++ getExAxioms fsn

getConStatus :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())] -> Conservativity
getConStatus oTh m fsn = min dataStatus defStatus
    where
        dataStatus = getDataStatus oTh m fsn
        defStatus = if null $ getOpsPredsAndExAxioms m fsn
                       ++ getOverlapQuery fsn
                    then Def
                    else Cons

getObligations :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getObligations m fsn = getOpsPredsAndExAxioms m fsn
  ++ getInfoSubsort m fsn ++ getOverlapQuery fsn

-- check the definitional form of the partial axioms
checkDefinitional :: Sign () () -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (Conservativity, [FORMULA ()])))
checkDefinitional osig fsn
    | elem Nothing l_Syms =
        let ax = head [ a | a <- axioms, isNothing $ leadingSym a ]
            ax' = quanti ax
            pos = snd $ leadingSymPos ax'
        in Just $ warning Nothing ("The following " ++ prettyType ax' ++
               " is not definitional:\n" ++ formatAxiom ax) pos
    | not $ null un_p_axioms =
        let ax = head $ filter (not . correctDef) $ filter containDef $
                 filter partialAxiom axioms
            ax' = head un_p_axioms
            pos = getRange $ take 1 un_p_axioms
        in Just $ warning Nothing ("The following partial " ++ prettyType ax' ++
               " is not definitional:\n" ++ formatAxiom ax) pos
    | length dom_l /= length (nubOrd dom_l) =
        let ax = head $ filter (`domainOs` dualOS) $
                 filter partialAxiom axioms
            ax' = head dualDom
            pos = getRange $ take 1 dualDom
            dualOS = head $ filter (\ o -> elem o $ delete o dom_l) dom_l
            dualDom = filter (`domainOs` dualOS) p_axioms
        in Just $ warning Nothing ("The following partial " ++ prettyType ax' ++
               " is not definitional:\n" ++ formatAxiom ax) pos
    | not $ null pcheck =
        let ax = head $ filter pcheckFunc $ filter (not . containDef) $
                 filter partialAxiom axioms
            ax' = head pcheck
            pos = getRange $ take 1 pcheck
        in Just $ warning Nothing ("The following partial " ++ prettyType ax' ++
               " is not definitional:\n" ++ formatAxiom ax) pos
    | otherwise = Nothing
    where
        formatAxiom :: FORMULA () -> String
        formatAxiom = flip showDoc "\n" . simplifyCASLSen osig
        axioms = getAxioms fsn
        l_Syms = map leadingSym axioms        -- leading_Symbol
        axioms' = map quanti axioms
        p_axioms = filter partialAxiom axioms'           -- all partial axioms
        pax_with_def = filter containDef p_axioms
        pax_without_def = filter (not . containDef) p_axioms
        un_p_axioms = filter (not . correctDef) pax_with_def
        dom_l = domainOpSymbs p_axioms
        pcheck = filter pcheckFunc pax_without_def
        pcheckFunc f = case leadingSym f of
                         Just (Left opS) -> elem opS dom_l
                         _ -> False

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
checkSort :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (Conservativity, [FORMULA ()])))
checkSort oTh@(osig, _) m fsn
    | null fsn && null nSorts = Just $ return (Just (Cons, []))
    | not $ null notFreeSorts =
        let Id ts _ pos = head notFreeSorts
            sname = concatMap tokStr ts
        in Just $ warning Nothing (sname ++ " is not freely generated") pos
    | not $ null nefsorts =
        let Id ts _ pos = head nefsorts
            sname = concatMap tokStr ts
        in Just $ warning (Just (Inconsistent, []))
                      (sname ++ " is not inhabited") pos
    | otherwise = Nothing
    where
        nSorts = getNSorts osig m
        notFreeSorts = getNotFreeSorts osig m fsn
        nefsorts = getNefsorts oTh m fsn

checkLeadingTerms :: [Named (FORMULA ())] -> Morphism () () ()
   -> [Named (FORMULA ())]
   -> Maybe (Result (Maybe (Conservativity, [FORMULA ()])))
checkLeadingTerms osens m fsn
    | not $ all (checkTerms tsig constructors) (map arguOfTerm leadingTerms) =
        let (Application os _ _) = tt
            tt = head $ filter (not . checkTerms tsig constructors .
                                    arguOfTerm) leadingTerms
            pos = axiomRangeforTerm axioms' tt
        in Just $ warning Nothing ("a leading term of " ++ opSymName os ++
           " consists of not only variables and constructors") pos
    | not $ all (checkTerms tsig constructors) (map arguOfPred leadingPreds) =
        let (Predication ps _ pos) = quanti pf
            pf = head $ filter (not . checkTerms tsig constructors .
                                    arguOfPred) leadingPreds
        in Just $
           warning Nothing ("a leading predicate of " ++ predSymName ps ++
           " consists of not only variables and constructors") pos
    | not $ all checkVarApp leadingTerms =
        let (Application os _ _) = tt
            tt = head $ filter (not . checkVarApp) leadingTerms
            pos = axiomRangeforTerm axioms' tt
        in Just $
           warning Nothing ("a variable occurs twice in a leading term of " ++
           opSymName os) pos
    | not $ all checkVarPred leadingPreds =
        let (Predication ps _ pos) = quanti pf
            pf = head $ filter (not . checkVarPred) leadingPreds
        in Just $
           warning Nothing ("a variable occurs twice in a leading " ++
           "predicate of " ++ predSymName ps) pos
    | otherwise = Nothing
    where
        tsig = mtarget m
        constructors = getConstructors osens m fsn
        axioms = getAxioms fsn
        axioms' = map quanti axioms
        ltp = map leadingTermPredication axioms'       -- leadingTermPred
        leadingTerms = concatMap (\ tp -> case tp of
                                             Just (Left t) -> [t]
                                             _ -> []) ltp      -- leading Term
        leadingPreds = concatMap (\ tp -> case tp of
                                             Just (Right f) -> [f]
                                             _ -> []) ltp

-- check the sufficient completeness
checkIncomplete :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (Conservativity, [FORMULA ()])))
checkIncomplete osens m fsn
    | not $ null notcomplete =
        let symb_p = leadingSymPos $ head $ head notcomplete
            pos = snd symb_p
            sname = case fmap extractLeadingSymb $ fst symb_p of
                      Just (Left opS) -> opSymName opS
                      Just (Right pS) -> predSymName pS
                      _ -> error "CASL.CCC.FreeTypes.<Symb_Name>"
        in Just $
           warning (Just (Cons, obligations)) ("the definition of " ++
           sname ++ " is not complete") pos
   | otherwise = Nothing
   where
       notcomplete = getNotComplete osens m fsn
       obligations = getObligations m fsn

checkTerminal :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> IO (Maybe (Result (Maybe (Conservativity, [FORMULA ()]))))
checkTerminal oTh m fsn = do
    let fs = getFs fsn
        fs_terminalProof = filter (\ f ->
          not $ isSortGen f || isMembership f || isExQuanti f || isDomain f
          ) fs
        domains = domainList fs
        obligations = getObligations m fsn
        conStatus = getConStatus oTh m fsn
        res = if null obligations then Nothing else
                  Just $ return (Just (conStatus, obligations))
    if null fs_terminalProof then return res else do
      proof <- terminationProof fs_terminalProof domains
      return $ case proof of
        Just True -> res
        _ -> Just $ warning (Just (Cons, obligations))
             (if isJust proof then "not terminating"
              else "cannot prove termination") nullRange

checkPositive :: [Named (FORMULA ())]
    -> Maybe (Result (Maybe (Conservativity, [FORMULA ()])))
checkPositive fsn
    | allPos = Just $ return (Just (Cons, []))
    | otherwise = Nothing
    where
        allPos = all checkPos $ getFs fsn
        checkPos :: FORMULA () -> Bool
        checkPos f =
            case quanti f of
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
checkFreeType :: (Sign () (), [Named (FORMULA ())]) -> Morphism () () ()
                 -> [Named (FORMULA ())]
                 -> IO (Result (Maybe (Conservativity, [FORMULA ()])))
checkFreeType oTh@(osig, osens) m axs = do
  ms <- mapM ($ axs)
    [ return . checkDefinitional osig
    , return . checkSort oTh m
    , return . checkLeadingTerms osens m
    , return . checkIncomplete osens m
    , checkTerminal oTh m
    , return . checkPositive]
  return $ case catMaybes ms of
    [] -> return $ Just (getConStatus oTh m axs, [])
    a : _ -> a

prettyType :: FORMULA () -> String
prettyType fm = case fm of
    Quantification {} -> "quantification"
    Junction j _ _ -> (if j == Con then "con" else "dis") ++ "junction"
    Relation _ c _ _ -> if c == Equivalence then "equivalence"
                                       else "implication"
    Negation _ _ -> "negation"
    Atom b _ -> (if b then "true" else "false") ++ " atom"
    Predication {} -> "predication"
    Definedness _ _ -> "definedness"
    Equation _ e _ _ -> (if e == Strong then "strong" else "existantial")
                         ++ " equation"
    Membership {} -> "membership"
    Mixfix_formula _ -> "mixfix formula"
    Unparsed_formula _ _ -> "unparsed formula"
    Sort_gen_ax _ _ -> "sort_gen_ax"
    QuantOp {} -> "forall op"
    QuantPred {} -> "forall pred"
    ExtFORMULA _ -> "extended formula"

{- | group the axioms according to their leading symbol,
output Nothing if there is some axiom in incorrect form -}
groupAxioms :: GetRange f => [FORMULA f]
  -> Maybe [(Either OP_SYMB PRED_SYMB, [FORMULA f])]
groupAxioms phis = do
  symbs <- mapM leadingSym phis
  return (filterA (zip symbs phis) [])
  where filterA [] _ = []
        filterA (p : ps) symb =
            let fp = fst p
                p' = if elem fp symb then []
                    else [(fp, snd $ unzip $ filter ((== fp) . fst) (p : ps))]
                symb' = if notElem fp symb then fp : symb else symb
            in p' ++ filterA ps symb'


filterOp :: Maybe (Either OP_SYMB PRED_SYMB) -> [(OP_NAME, OpType)]
filterOp symb = case symb of
                  Just (Left (Qual_op_name ident (Op_type k ags rs _) _)) ->
                      [(ident, OpType {opKind = k, opArgs = ags, opRes = rs})]
                  _ -> []


filterPred :: Maybe (Either OP_SYMB PRED_SYMB) -> [(OP_NAME, PredType)]
filterPred symb = case symb of
                    Just (Right (Qual_pred_name ident (Pred_type s _) _)) ->
                        [(ident, PredType {predArgs = s})]
                    _ -> []


{- | a leading term and a predication consist of
variables and constructors only -}
checkTerms :: Sign f e -> [OP_SYMB] -> [TERM f] -> Bool
checkTerms sig cons = all checkT
  where checkT t = case unsortedTerm t of
          Qual_var {} -> True
          Application subop subts _ ->
            isCons sig cons subop && all checkT subts
          _ -> False


-- |  no variable occurs twice in a leading term
checkVarApp :: Ord f => TERM f -> Bool
checkVarApp (Application _ ts _) = noDuplation $ concatMap varOfTerm ts
checkVarApp _ = error "CASL.CCC.FreeTypes<checkVarApp>"

-- |  no variable occurs twice in a leading predication
checkVarPred :: Ord f => FORMULA f -> Bool
checkVarPred (Predication _ ts _) = noDuplation $ concatMap varOfTerm ts
checkVarPred _ = error "CASL.CCC.FreeTypes<checkVarPred>"

-- | there are no duplicate items in a list
noDuplation :: Ord a => [a] -> Bool
noDuplation l = length (nubOrd l) == length l

-- | create all possible pairs from a list
pairs :: [a] -> [(a, a)]
pairs ps = case ps of
  hd : tl@(_ : _) -> map (\ x -> (hd, x)) tl ++ pairs tl
  _ -> []

-- | get the patterns of a term
patternsOfTerm :: TERM f -> [TERM f]
patternsOfTerm t = case unsortedTerm t of
    Qual_var {} -> [t]
    Application (Qual_op_name {}) ts _ -> ts
    _ -> []

-- | get the patterns of a axiom
patternsOfAxiom :: FORMULA f -> [TERM f]
patternsOfAxiom f = case quanti f of
    Negation f' _ -> patternsOfAxiom f'
    Relation _ c f' _ | c /= Equivalence -> patternsOfAxiom f'
    Relation f' Equivalence _ _ -> patternsOfAxiom f'
    Predication _ ts _ -> ts
    Equation t _ _ _ -> patternsOfTerm t
    _ -> []


-- | check whether two patterns are overlapped
checkPatterns :: (Eq f) => ([TERM f], [TERM f]) -> Bool
checkPatterns (ps1, ps2) = case (ps1, ps2) of
  (hd1 : tl1, hd2 : tl2) ->
      if isVar hd1 || isVar hd2 then checkPatterns (tl1, tl2)
      else sameOpsApp hd1 hd2 && checkPatterns (patternsOfTerm hd1 ++ tl1,
                                                patternsOfTerm hd2 ++ tl2)
  _ -> True

{- | get the axiom from left hand side of a implication,
if there is no implication, then return atomic formula true -}
conditionAxiom :: FORMULA f -> [FORMULA f]
conditionAxiom f = case quanti f of
                     Relation f' c _ _ | c /= Equivalence -> [f']
                     _ -> [trueForm]

{- | get the axiom from right hand side of a equivalence,
if there is no equivalence, then return atomic formula true -}
resultAxiom :: FORMULA f -> [FORMULA f]
resultAxiom f = case quanti f of
                  Relation _ c f' _ | c /= Equivalence -> resultAxiom f'
                  Relation _ Equivalence f' _ -> [f']
                  _ -> [trueForm]

{- | get the term from left hand side of a equation in a formula,
if there is no equation, then return a simple id -}
resultTerm :: FORMULA f -> [TERM f]
resultTerm f = case quanti f of
                 Relation _ c f' _ | c /= Equivalence -> resultTerm f'
                 Negation (Definedness _ _) _ ->
                   [varOrConst (mkSimpleId "undefined")]
                 Equation _ _ t _ -> [t]
                 _ -> [varOrConst (mkSimpleId "unknown")]

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
      where cond = concatMap conditionAxiom [a1, a2]
            resT = concatMap resultTerm [a1, a2]
            resA = concatMap resultAxiom [a1, a2]
            con1 = substiF s1 $ head cond
            con2 = substiF s2 $ last cond
            resT1 = substitute s1 $ head resT
            resT2 = substitute s2 $ last resT
            resA1 = substiF s1 $ head resA
            resA2 = substiF s2 $ last resA

-- | check whether the patterns of a function or predicate are complete
completePatterns :: [OP_SYMB] -> [[TERM ()]] -> Bool
completePatterns cons pas
    | all null pas = True
    | all isVar $ map head pas = completePatterns cons (map tail pas)
    | otherwise = elem (con_ts $ map head pas) s_cons &&
                  all id (map (completePatterns cons) $ pa_group pas)
    where s_op_os c = case c of
                        Op_name _ -> []
                        Qual_op_name on ot _ -> [(res_OP_TYPE ot, on)]
          s_sum sns = map (\ s -> (s, map snd $
                      filter (\ c -> fst c == s) sns)) $ nubOrd $ map fst sns
          s_cons = s_sum $ concatMap s_op_os cons
          s_op_t t = case t of
                       Application os _ _ -> s_op_os os
                       _ -> []
          con_ts = head . s_sum . concatMap s_op_t
          opN t = case t of
                    Application os _ _ -> opSymbName os
                    _ -> genName "unknown"
          pa_group p = map (p_g . (\ o ->
             filter (\ a -> isVar (head a) || opN (head a) == o) p))
               $ snd $ head $ filter (\ sc ->
                   fst sc == sortOfTerm (head $ head p)) s_cons
          p_g p = map (\ p' ->
            if isVar $ head p'
            then replicate (maximum $ map
                   (length . arguOfTerm . head) p) (head p') ++ tail p'
            else arguOfTerm (head p') ++ tail p') p

{- |
Module      :  $Header$
Description :  consistency checking of free types
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Consistency checking of free types
-}

module CASL.CCC.FreeTypes (checkFreeType) where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof
import Common.AS_Annotation
import Common.Consistency
import Common.Result
import Common.Id
import Data.List (nub,intersect,delete)
import Data.Maybe (isJust, fromJust)

inhabited :: [SORT] -> [Constraint] -> [SORT]
inhabited sorts constrs = iterateInhabited sorts
    where (_,ops,_)=recover_Sort_gen_ax constrs
          argsRes=concatMap (\os-> case os of
                                 Op_name _->[]
                                 Qual_op_name _ ot _->
                                     case ot of
                                       Op_type _ args res _ -> [(args,res)]
                        ) ops
          iterateInhabited l =
                    if l==newL then newL else iterateInhabited newL
                            where newL =foldr (\(ags,rs) l'->
                                                  if all (\s->elem s l') ags
                                                      && not (elem rs l')
                                                  then rs:l'
                                                  else l') l argsRes

getFs :: [Named (FORMULA ())] -> [FORMULA ()]
getFs = map sentence . filter is_user_or_sort_gen

getOfs:: [Named (FORMULA ())] -> [FORMULA ()]
getOfs = map sentence . filter is_user_or_sort_gen

getExAxioms :: [Named (FORMULA ())] -> [FORMULA ()]
getExAxioms = filter is_ex_quanti . getFs

getAxioms :: [Named (FORMULA ())] -> [FORMULA ()]
getAxioms = filter (\f-> (not $ isSortGen f) &&
                             (not $ is_Membership f) &&
                             (not $ is_ex_quanti f)) . getFs

getInfoSubsort :: Morphism () () ()
    -> [Named (FORMULA ())] -> [FORMULA ()]
getInfoSubsort m fsn = info_subsort
    where
        fs = getFs fsn
        memberships = filter (\f-> is_Membership f) fs
        tsig = mtarget m
        esorts = Set.toList $ emptySortSet tsig
        info_subsort = concatMap (infoSubsort esorts) memberships

getAxGroup :: [Named (FORMULA ())]
    -> Maybe [(Either OP_SYMB PRED_SYMB, [FORMULA ()])]
getAxGroup fsn = axGroup
    where
        axioms = getAxioms fsn
        _axioms = map quanti axioms
        ax_without_dom = filter (not.isDomain) _axioms
        axGroup = groupAxioms ax_without_dom

getConstructors :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())] -> [OP_SYMB]
getConstructors osens m fsn = constructors
    where
        fs = getFs fsn
        ofs = getOfs osens
        tsig = mtarget m
        fconstrs = concatMap constraintOfAxiom (ofs ++ fs)
        (_,constructors_o,_) = recover_Sort_gen_ax fconstrs
        constructors = constructorOverload tsig (opMap tsig) constructors_o
{-
   check that patterns do not overlap, if not, return proof obligation.
-}
getOverlapQuery :: [Named (FORMULA ())] -> [FORMULA ()]
getOverlapQuery fsn = overlap_query
    where
        axGroup = getAxGroup fsn
        axPairs =
            case axGroup of
              Just sym_fs -> concatMap pairs $ map snd sym_fs
              Nothing -> error "CASL.CCC.FreeTypes.<axPairs>"
        olPairs = filter (\ (a, b) -> checkPatterns
                           (patternsOfAxiom a,
                            patternsOfAxiom b)) axPairs
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
        overlap_query = map (\f-> Quantification Universal
                                                  (varDeclOfF f)
                                                  f
                                                  nullRange) overlap_qu

{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getOOps :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getOOps m fsn = oOps
    where
        sig = imageOfMorphism m
        oldOpMap = opMap sig
        axioms = getAxioms fsn
        op_fs = filter (\f-> case leadingSym f of
                               Just (Left _) -> True
                               _ -> False) axioms
        find_ot (ident,ot) = case Map.lookup ident oldOpMap of
                               Nothing -> False
                               Just ots -> Set.member ot ots
        oOps = filter (\a-> find_ot $ head $ filterOp $ leadingSym a) op_fs

{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getOPreds :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getOPreds m fsn = oPreds
    where
       sig = imageOfMorphism m
       oldPredMap = predMap sig
       axioms = getAxioms fsn
       pred_fs = filter (\f-> case leadingSym f of
                                Just (Right _) -> True
                                _ -> False) axioms
       find_pt (ident,pt) = case Map.lookup ident oldPredMap of
                                Nothing -> False
                                Just pts -> Set.member pt pts
       oPreds = filter (\a-> find_pt $ head $ filterPred $ leadingSym a) pred_fs

getNSorts :: Sign () () -> Morphism () () () -> [Id]
getNSorts osig m = nSorts
    where
        tsig = mtarget m
        oldSorts = sortSet osig
        allSorts = sortSet tsig
        newSorts = Set.filter (\s-> not $ Set.member s oldSorts) allSorts
        nSorts = Set.toList newSorts

getDataStatus :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())] -> ConsistencyStatus
getDataStatus (osig,osens) m fsn = dataStatus
    where
        fs = getFs fsn
        ofs = getOfs osens
        tsig = mtarget m
        sR = Rel.toList $ sortRel tsig
        subs = map fst sR
        nSorts = getNSorts osig m
        fconstrs = concatMap constraintOfAxiom (ofs ++ fs)
        (srts,_,_) = recover_Sort_gen_ax fconstrs
        gens = intersect nSorts srts
        dataStatus = if null nSorts then Definitional
                     else if not $ null $ filter (\s-> (not $ elem s subs) &&
                             (not $ elem s gens)) nSorts
                     then Conservative
                     else Monomorphic

getNotComplete :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())] -> [[FORMULA ()]]
getNotComplete osens m fsn = not_complete
    where
        constructors = getConstructors osens m fsn
        axGroup = getAxGroup fsn
        axGroups = case axGroup of
                       Just sym_fs -> map snd sym_fs
                       Nothing -> error "CASL.CCC.FreeTypes.<axGroups>"
        not_complete = filter (\f'-> not $ completePatterns constructors $
                                    map patternsOfAxiom f') axGroups

getConStatus :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())] -> ConsistencyStatus
getConStatus (osig,osens) m fsn = conStatus
    where
        dataStatus = getDataStatus (osig,osens) m fsn
        ex_axioms = getExAxioms fsn
        oOps = getOOps m fsn
        oPreds = getOPreds m fsn
        overlap_query = getOverlapQuery fsn
        defStatus = if null (oOps ++ oPreds ++ ex_axioms ++ overlap_query)
                    then Definitional
                    else Conservative
        conStatus = min dataStatus defStatus

getObligations :: Morphism () () () -> [Named (FORMULA ())] -> [FORMULA ()]
getObligations m fsn = obligations
    where
        ex_axioms = getExAxioms fsn
        oOps = getOOps m fsn
        oPreds = getOPreds m fsn
        info_subsort = getInfoSubsort m fsn
        overlap_query = getOverlapQuery fsn
        obligations = oOps ++ oPreds ++ ex_axioms ++ info_subsort ++
                      overlap_query

{-
   check the definitional form of the partial axioms
-}
checkDefinitional :: [Named (FORMULA ())]
    -> Maybe (Result (Maybe (ConsistencyStatus,[FORMULA ()])))
checkDefinitional fsn
    | elem Nothing l_Syms =
        let pos = snd $ head $ filter (\f'-> fst f' == Nothing) $
                  map leadingSymPos _axioms
        in Just $ warning Nothing "axiom is not definitional" pos
    | not $ null un_p_axioms =
        let pos = getRange $ take 1 un_p_axioms
        in Just $ warning Nothing "partial axiom is not definitional" pos
    | length dom_l /= (length $ nub dom_l) =
        let pos = getRange $ take 1 dualDom
            dualOS = head $ filter (\o-> elem o $ delete o dom_l) dom_l
            dualDom = filter (\f-> domain_os f dualOS) p_axioms
        in Just $ warning Nothing "partial axiom is not definitional" pos
    | not $ null pcheck =
        let pos = getRange $ take 1 pcheck
        in Just $ warning Nothing "partial axiom is not definitional" pos
    | otherwise = Nothing
    where
        axioms = getAxioms fsn
        l_Syms = map leadingSym axioms        -- leading_Symbol
        _axioms = map quanti axioms
        p_axioms = filter partialAxiom _axioms           -- all partial axioms
        pax_with_def = filter containDef p_axioms
        pax_without_def = filter (not.containDef) p_axioms
        un_p_axioms = filter (not.correctDef) pax_with_def
        dom_l = domainOpSymbs p_axioms
        pcheck = filter (\f-> case leadingSym f of
                                  Just (Left opS) -> elem opS dom_l
                                  _               -> False) pax_without_def

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
checkSort :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (ConsistencyStatus,[FORMULA ()])))
checkSort (osig,osens) m fsn
    | null fsn && null nSorts = Just $ return (Just (Conservative,[]))
    | not $ null notFreeSorts =
        let (Id ts _ pos) = head notFreeSorts
            sname = concatMap tokStr ts
        in Just $ warning Nothing (sname ++ " is not freely generated") pos
    | not $ null nefsorts =
        let (Id ts _ pos) = head nefsorts
            sname = concatMap tokStr ts
        in Just $
             warning (Just (Inconsistent,[])) (sname ++ " is not inhabited") pos
    | otherwise = Nothing
    where
        fs = getFs fsn
        ofs = getOfs osens
        tsig = mtarget m
        oldSorts = sortSet osig
        oSorts = Set.toList oldSorts
        esorts = Set.toList $ emptySortSet tsig
        nSorts = getNSorts osig m
        axOfS = filter (\f-> isSortGen f || is_Membership f) fs
        notFreeSorts = filter (\s->is_free_gen_sort s axOfS ==Just False) nSorts
        fconstrs = concatMap constraintOfAxiom (ofs ++ fs)
        (srts,_,_) = recover_Sort_gen_ax fconstrs
        f_Inhabited = inhabited oSorts fconstrs
        fsorts = filter (\s-> not $ elem s esorts) $ intersect nSorts srts
        nefsorts = filter (\s->not $ elem s f_Inhabited) fsorts

checkLeadingTerms :: [Named (FORMULA ())] -> Morphism () () ()
   -> [Named (FORMULA ())]
   -> Maybe (Result (Maybe (ConsistencyStatus,[FORMULA ()])))
checkLeadingTerms osens m fsn
    | not $ all (checkTerms tsig constructors) (map arguOfTerm leadingTerms) =
        let (Application os _ _) = tt
            tt = head $ filter (\t->not $ checkTerms tsig constructors $
                                    arguOfTerm t) leadingTerms
            pos = axiomRangeforTerm _axioms tt
        in Just $ warning Nothing ("a leading term of " ++ opSymName os ++
           " consists of not only variables and constructors") pos
    | not $ all (checkTerms tsig constructors) (map arguOfPred leadingPreds) =
        let (Predication ps _ pos) = quanti pf
            pf = head $ filter (\p->not $ checkTerms tsig constructors $
                                    arguOfPred p) leadingPreds
        in Just $
           warning Nothing ("a leading predicate of " ++ predSymName ps ++
           " consists of not only variables and constructors") pos
    | not $ all checkVar_App leadingTerms =
        let (Application os _ _) = tt
            tt = head $ filter (\t->not $ checkVar_App t) leadingTerms
            pos = axiomRangeforTerm _axioms tt
        in Just $
           warning Nothing ("a variable occurs twice in a leading term of " ++
           opSymName os) pos
    | not $ all checkVar_Pred leadingPreds =
        let (Predication ps _ pos) = quanti pf
            pf = head $ filter (\p->not $ checkVar_Pred p) leadingPreds
        in Just $ warning Nothing ("a variable occurs twice in a leading " ++
           "predicate of " ++ predSymName ps) pos
    | otherwise = Nothing
    where
        tsig = mtarget m
        constructors = getConstructors osens m fsn
        axioms = getAxioms fsn
        _axioms = map quanti axioms
        ltp = map leading_Term_Predication _axioms       --  leading_term_pred
        leadingTerms = concatMap (\tp->case tp of
                                             Just (Left t)->[t]
                                             _ -> []) ltp      -- leading Term
        leadingPreds = concatMap (\tp->case tp of
                                             Just (Right f)->[f]
                                             _ -> []) ltp

{-
   check the sufficient completeness
-}
checkIncomplete :: [Named (FORMULA ())] -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (ConsistencyStatus,[FORMULA ()])))
checkIncomplete osens m fsn
    | not $ null notcomplete =
        let symb_p = leadingSymPos $ head $ head notcomplete
            pos = snd symb_p
            sname = case (fst symb_p) of
                      Just (Left opS) -> opSymName opS
                      Just (Right pS) -> predSymName pS
                      _ -> error "CASL.CCC.FreeTypes.<Symb_Name>"
        in Just $
           warning (Just (Conservative,obligations)) ("the definition of " ++
           sname ++ " is not complete") pos
   | otherwise = Nothing
   where
       notcomplete = getNotComplete osens m fsn
       obligations = getObligations m fsn

checkTerminal  :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
    -> [Named (FORMULA ())]
    -> Maybe (Result (Maybe (ConsistencyStatus,[FORMULA ()])))
checkTerminal (osig,osens) m fsn
    | (not $ null fs_terminalProof) && (proof /= Just True)=
        if proof == Just False
            then Just $ warning (Just (Conservative,obligations))
                 "not terminating" nullRange
            else Just $ warning (Just (Conservative,obligations))
                 "cannot prove termination" nullRange
    | not $ null obligations = Just $ return (Just (conStatus,obligations))
    | otherwise = Nothing
    where
        fs = getFs fsn
        fs_terminalProof = filter (\f->(not $ isSortGen f) &&
                                       (not $ is_Membership f) &&
                                       (not $ is_ex_quanti f) &&
                                       (not $ isDomain f)) fs
        domains = domainList fs
        proof = terminationProof fs_terminalProof domains
        obligations = getObligations m fsn
        conStatus = getConStatus (osig,osens) m fsn

{------------------------------------------------------------------------
   function checkFreeType:
   - check if leading symbols are new (not in the image of morphism),
           if not, return them as obligations
   - generated datatype is free
   - if new sort is not etype or esort, it can not be empty.
   - the leading terms consist of variables and constructors only,
           if not, return Nothing
     - split function leading_Symb into
       leading_Term_Predication
       and
       extract_leading_symb
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
-------------------------------------------------------------------------}
-- | free datatypes and recursive equations are consistent
checkFreeType :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
                 -> [Named (FORMULA ())]
                 -> Result (Maybe (ConsistencyStatus,[FORMULA ()]))
checkFreeType (osig,osens) m fsn
    | isJust definitional = fromJust definitional
    | isJust sort         = fromJust sort
    | isJust leadingTerms = fromJust leadingTerms
    | isJust incomplete   = fromJust incomplete
    | isJust terminal     = fromJust terminal
    | otherwise           = return (Just (conStatus,[]))
    where
        definitional = checkDefinitional fsn
        sort         = checkSort (osig,osens) m fsn
        leadingTerms = checkLeadingTerms osens m fsn
        incomplete   = checkIncomplete osens m fsn
        terminal     = checkTerminal (osig,osens) m fsn
        conStatus    = getConStatus (osig,osens) m fsn

-- | group the axioms according to their leading symbol,
--   output Nothing if there is some axiom in incorrect form
groupAxioms :: [FORMULA f] -> Maybe [(Either OP_SYMB PRED_SYMB,[FORMULA f])]
groupAxioms phis = do
  symbs <- mapM leadingSym phis
  return (filterA (zip symbs phis) [])
  where filterA [] _=[]
        filterA (p:ps) symb=
            let fp=fst p
                p'= if elem fp symb then []
                    else [(fp,snd $ unzip $ filter (\x->fst x == fp) (p:ps))]
                symb'= if not $ elem fp symb then fp:symb
                       else symb
            in p' ++ filterA ps symb'


filterOp :: Maybe (Either OP_SYMB PRED_SYMB) -> [(OP_NAME,OpType)]
filterOp symb = case symb of
                  Just (Left (Qual_op_name ident (Op_type k ags rs _) _))->
                      [(ident, OpType {opKind=k, opArgs=ags, opRes=rs})]
                  _ -> []


filterPred :: Maybe (Either OP_SYMB PRED_SYMB) -> [(OP_NAME,PredType)]
filterPred symb = case symb of
                    Just (Right (Qual_pred_name ident (Pred_type s _) _)) ->
                        [(ident, PredType {predArgs=s})]
                    _ -> []


-- | a leading term and a predication consist of
-- | variables and constructors only
checkTerms :: Sign f e -> [OP_SYMB] -> [TERM f] -> Bool
checkTerms sig cons ts = all checkT ts
  where checkT (Sorted_term tt _ _) = checkT tt
        checkT (Qual_var _ _ _) = True
        checkT (Application subop subts _) =
            isCons sig cons subop && all checkT subts
        checkT _ = False


-- |  no variable occurs twice in a leading term
checkVar_App :: (Eq f) => TERM f -> Bool
checkVar_App (Application _ ts _) = noDuplation $ concatMap varOfTerm ts
checkVar_App _ = error "CASL.CCC.FreeTypes<checkVar_App>"

-- |  no variable occurs twice in a leading predication
checkVar_Pred :: (Eq f) => FORMULA f -> Bool
checkVar_Pred (Predication _ ts _) = noDuplation $ concatMap varOfTerm ts
checkVar_Pred _ = error "CASL.CCC.FreeTypes<checkVar_Pred>"

-- | there are no duplicate items in a list
noDuplation :: (Eq a) => [a] -> Bool
noDuplation l = length (nub l) == length l

-- | create all possible pairs from a list
pairs :: [a] -> [(a, a)]
pairs ps = case ps of
  hd : tl@(_ : _) -> map (\ x -> (hd, x)) tl ++ pairs tl
  _ -> []

-- | get the patterns of a term
patternsOfTerm :: TERM f -> [TERM f]
patternsOfTerm t = case t of
                     Qual_var _ _ _ -> [t]
                     Application (Qual_op_name _ _ _) ts _-> ts
                     Sorted_term t' _ _ -> patternsOfTerm t'
                     Cast t' _ _ -> patternsOfTerm t'
                     _ -> []


-- | get the patterns of a axiom
patternsOfAxiom :: FORMULA f -> [TERM f]
patternsOfAxiom f = case f of
                      Quantification _ _ f' _ -> patternsOfAxiom f'
                      Negation f' _ -> patternsOfAxiom f'
                      Implication _ f' _ _ -> patternsOfAxiom f'
                      Equivalence f' _ _ -> patternsOfAxiom f'
                      Predication _ ts _ -> ts
                      Existl_equation t _ _ -> patternsOfTerm t
                      Strong_equation t _ _ -> patternsOfTerm t
                      _ -> []


-- | check whether two patterns are overlapped
checkPatterns :: (Eq f) => ([TERM f],[TERM f]) -> Bool
checkPatterns (ps1,ps2)
        | ps1 == ps2 = True
        | (isVar $ head ps1) ||
          (isVar $ head ps2) = checkPatterns (tail ps1,tail ps2)
        | otherwise = sameOps_App (head ps1) (head ps2) &&
                        checkPatterns ((patternsOfTerm $ head ps1) ++ tail ps1,
                                       (patternsOfTerm $ head ps2) ++ tail ps2)


-- | get the axiom from left hand side of a implication,
-- | if there is no implication, then return atomic formula true
conditionAxiom ::  FORMULA f -> [FORMULA f]
conditionAxiom f = case f of
                     Quantification _ _ f' _ -> conditionAxiom f'
                     Implication f' _ _ _ -> [f']
                     _ -> [True_atom nullRange]


-- | get the axiom from right hand side of a equivalence,
-- | if there is no equivalence, then return atomic formula true
resultAxiom ::  FORMULA f -> [FORMULA f]
resultAxiom f = case f of
                  Quantification _ _ f' _ -> resultAxiom f'
                  Implication _ f' _ _ -> resultAxiom f'
                  Equivalence _ f' _ -> [f']
                  _ -> [True_atom nullRange]


-- | get the term from left hand side of a equation in a formula,
-- | if there is no equation, then return a simple id
resultTerm :: FORMULA f -> [TERM f]
resultTerm f = case f of
                 Quantification _ _ f' _ -> resultTerm f'
                 Implication _ f' _ _ -> resultTerm f'
                 Negation (Definedness _ _) _ ->
                   [varOrConst (mkSimpleId "undefined")]
                 Strong_equation _ t _ -> [t]
                 Existl_equation _ t _ -> [t]
                 _ -> [varOrConst (mkSimpleId "unknown")]

-- | create the proof obligation for a pair of overlapped formulas
overlapQuery :: Eq f => ((FORMULA f,[(TERM f,TERM f)]),
                         (FORMULA f,[(TERM f,TERM f)])) -> FORMULA f
overlapQuery ((a1,s1),(a2,s2)) =
        case leadingSym a1 of
          Just (Left _)
            | containNeg a1 && (not $ containNeg a2) ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Negation (Definedness resT2 nullRange)
                                      nullRange)
                            True
                            nullRange
            | containNeg a2 && (not $ containNeg a1) ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Negation (Definedness resT1 nullRange)
                                      nullRange)
                            True
                            nullRange
            | containNeg a1 && containNeg a2 ->
                True_atom nullRange
            | otherwise ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Strong_equation resT1 resT2 nullRange)
                            True
                            nullRange
          Just (Right _)
            | containNeg a1 && (not $ containNeg a2) ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Negation resA2 nullRange)
                            True
                            nullRange
            | containNeg a2 && (not $ containNeg a1) ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Negation resA1 nullRange)
                            True
                            nullRange
            | containNeg a1 && containNeg a2 ->
                True_atom nullRange
            | otherwise ->
                Implication (Conjunction [con1,con2] nullRange)
                            (Conjunction [resA1,resA2] nullRange)
                            True
                            nullRange
          _ -> error "CASL.CCC.FreeTypes.<overlapQuery>"
      where cond = concatMap conditionAxiom [a1,a2]
            resT = concatMap resultTerm [a1,a2]
            resA = concatMap resultAxiom [a1,a2]
            con1 = substiF s1 $ head cond
            con2 = substiF s2 $ last cond
            resT1 = substitute s1 $ head resT
            resT2 = substitute s2 $ last resT
            resA1 = substiF s1 $ head resA
            resA2 = substiF s2 $ last resA


-- | check whether the patterns of a function or predicate are complete
completePatterns :: (Eq f) => [OP_SYMB] -> ([[TERM f]]) -> Bool
completePatterns cons pas
    | all null pas = True
    | all isVar $ map head pas = completePatterns cons (map tail pas)
    | otherwise = elem (con_ts $ map head pas) s_cons &&
                  (all id $ map (completePatterns cons) $ pa_group pas)
    where s_op_os c = case c of
                        Op_name _ -> []
                        Qual_op_name on ot _ -> [(res_OP_TYPE ot,on)]
          s_sum sns = map (\s->(s, map snd $ filter (\c-> fst c == s) sns)) $
                      nub $ map fst sns
          s_cons = s_sum $ concatMap s_op_os cons
          s_op_t t = case t of
                       Application os _ _ -> s_op_os os
                       _ -> []
          con_ts = head . s_sum . concatMap s_op_t
          opN t = case t of
                    Application os _ _ -> opSymbName os
                    _ -> genName "unknown"
          pa_group p = map (p_g . (\o->
                         filter (\a-> (isVar $ head a) ||
                                      ((opN $ head a) == o)) p))
                         (snd $ head $ filter (\sc-> fst sc == (sortOfTerm $
                                                  head $ head p)) s_cons)
          p_g p = map (\p'-> if isVar $ head p'
                             then replicate (maximum $ map
                                (length.arguOfTerm.head) p) (head p') ++ tail p'
                             else (arguOfTerm $ head p') ++ tail p') p

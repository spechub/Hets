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


{------------------------------------------------------------------------
"free datatypes and recursive equations are consistent"

checkFreeType :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
                 -> [Named (FORMULA ())] -> Result (Maybe (Bool,[FORMULA ()]))
Just (Just True) => Yes, is consistent
Just (Just False) => No, is inconsistent
Just Nothing => don't know
------------------------------------------------------------------------}

module CASL.CCC.FreeTypes where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Data.Map as Map
import qualified Data.Set as Set
-- import qualified Common.Lib.Rel as Rel
import CASL.CCC.SignFuns
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof
import Common.AS_Annotation
import Common.DocUtils
import Common.Result
import Common.Id
import Maybe
import Debug.Trace
import Data.List (nub,intersect,delete)


{------------------------------------------------------------------------
   function checkFreeType:
   - check if leading symbols are new (not in the image of morphism),
           if not, return Nothing
   - the leading terms consist of variables and constructors only,
           if not, return Nothing
     - split function leading_Symb into
       leading_Term_Predication
       and
       extract_leading_symb
     - collect all operation symbols from recover_Sort_gen_ax fconstrs
                                                       (= constructors)
   - no variable occurs twice in a leading term, if not, return Nothing
   - check that patterns do not overlap, if not, return Nothing This means:
       in each group of the grouped axioms:
       all patterns of leading terms/formulas are disjoint
       this means: either leading symbol is a variable,
                           and there is just one axiom
                   otherwise, group axioms according to leading symbol
                              no symbol may be a variable
                              check recursively the arguments of
                              constructor in each group
  - termination proof
  - return (Just True)
-------------------------------------------------------------------------}
-- | free datatypes and recursive equations are consistent
checkFreeType :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
                 -> [Named (FORMULA ())] -> Result (Maybe (Bool,[FORMULA ()]))
checkFreeType (osig,osens) m fsn
    | not $ null notFreeSorts =
        let (Id ts _ pos) = head notFreeSorts
            sname = concat $ map tokStr ts
        in warning Nothing (sname ++ " is not freely generated") pos
    | any (\s->not $ elem s f_Inhabited) $ intersect nSorts srts =
        let (Id ts _ pos) = head $ filter (\s->not $ elem s f_Inhabited) nSorts
            sname = concat $ map tokStr ts
        in warning (Just (False,[])) (sname ++ " is not inhabited") pos
    | elem Nothing l_Syms =
        let pos = snd $ head $ filter (\f'-> (fst f') == Nothing) $
                  map leadingSymPos _axioms
        in warning Nothing "axiom is not definitional" pos
    | not $ null $ un_p_axioms =
        let pos = posOf $ (take 1 un_p_axioms)
        in warning Nothing "partial axiom is not definitional" pos
    | (length dom_l) /= (length $ nub $ dom_l) =
        let pos = posOf $ (take 1 dualDom)
            dualOS = head $ filter (\o-> elem o $ delete o dom_l) dom_l
            dualDom = filter (\f-> domain_os f dualOS) p_axioms
        in warning Nothing "partial axiom is not definitional" pos    
    | not $ null $ pcheck =
        let pos = posOf $ (take 1 pcheck)
        in warning Nothing "partial axiom is not definitional" pos
    | any id $ map find_ot id_ots =
        let pos = old_op_ps
        in warning Nothing ("Operation: " ++ old_op_id ++ " is not new") pos
    | any id $ map find_pt id_pts =
        let pos = old_pred_ps
        in warning Nothing ("Predication: " ++old_pred_id++ " is not new") pos
    | not $ and $ map (checkTerms tsig constructors) $ 
      map arguOfTerm leadingTerms=
        let (Application os _ _) = tt
            tt= head $ filter (\t->not $ checkTerms tsig constructors $ 
                                   arguOfTerm t) $ leadingTerms
            pos = axiomRangeforTerm _axioms tt 
        in warning Nothing ("a leading term of " ++ (opSymStr os) ++
           " consists of not only variables and constructors") pos          
    | not $ and $ map (checkTerms tsig constructors) $ 
      map arguOfPred leadingPreds=
        let (Predication ps _ pos) = quanti pf
            pf= head $ filter (\p->not $ checkTerms tsig constructors $ 
                                   arguOfPred p) $ leadingPreds
        in warning Nothing ("a leading predication of " ++ (predSymStr ps) ++
           " consists of not only variables and constructors") pos           
    | not $ and $ map checkVar_App leadingTerms =
        let (Application os _ _) = tt
            tt = head $ filter (\t->not $ checkVar_App t) leadingTerms
            pos = axiomRangeforTerm _axioms tt
        in warning Nothing ("a variable occurs twice in a leading term of " ++
                            opSymStr os) pos
    | (not $ null fs_terminalProof) && (proof /= Just True)= 
         if proof == Just False 
         then warning Nothing "not terminating" nullRange
         else warning Nothing "cannot prove termination" nullRange
    | not $ ((null (info_subsort ++ overlap_query ++ ex_axioms)) &&
             (null subSortsF)) =
        return (Just (True,(overlap_query ++
                            ex_axioms ++
                            (concat $ map snd subSortsF) ++ 
                            info_subsort)))
    | otherwise = return (Just (True,[]))
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
    where
    fs1 = map sentence (filter is_user_or_sort_gen fsn)
    fs = trace (showDoc fs1 "new formulars") fs1     -- new formulars
    fs_terminalProof = filter (\f->(not $ isSortGen f) &&
                                   (not $ is_Membership f) &&
                                   (not $ is_ex_quanti f) &&
                                   (not $ isDomain f)) fs
    ofs = map sentence (filter is_user_or_sort_gen osens)
    sig = imageOfMorphism m
    tsig = mtarget m
    oldSorts1 = Set.union (sortSet sig) (sortSet osig)
    oldSorts = trace (showDoc oldSorts1 "old sorts") oldSorts1  -- old sorts
    oSorts = Set.toList oldSorts
    allSorts1 = sortSet $ tsig
    allSorts = trace (showDoc allSorts1 "all sorts") allSorts1
    newSorts1 = Set.filter (\s-> not $ Set.member s oldSorts) allSorts
                                                          -- new sorts
    newSorts = trace (showDoc newSorts1 "new sorts") newSorts1
    nSorts = Set.toList newSorts
    oldOpMap1 = opMap sig
    oldOpMap = trace (showDoc oldOpMap1 "oldOPMap") oldOpMap1
    oldPredMap1 = predMap sig
    oldPredMap = trace (showDoc oldPredMap1 "oldPredMap") oldPredMap1
    fconstrs = concat $ map constraintOfAxiom (ofs ++ fs)
    (srts1,constructors1,_) = recover_Sort_gen_ax fconstrs
    srts = trace (showDoc srts1 "srts from constraint") srts1      --   srts
    constructors_o = trace (showDoc constructors1 "constrs_orig") constructors1
                                                           -- constructors
    op_map1 = opMap $ tsig 
    op_map = trace (showDoc op_map1 "op_map") op_map1
    constructors2 = constructorOverload tsig op_map constructors_o

    constructors = trace (showDoc constructors2 "constrs+overl") constructors2
    f_Inhabited1 = inhabited oSorts fconstrs
    f_Inhabited = trace (showDoc f_Inhabited1 "f_inhabited" ) f_Inhabited1
                                                             --  f_inhabited
    axOfS = filter (\f-> (isSortGen f) ||
                         (is_Membership f)) fs
    axioms1 = filter (\f-> (not $ isSortGen f) &&
                           (not $ is_Membership f)) fs
    memberships1 = filter (\f-> is_Membership f) fs
    memberships = trace (showDoc memberships1 "memberships") memberships1
    info_subsort1 = map infoSubsort memberships
    info_subsort = trace (showDoc info_subsort1 "infoSubsort") info_subsort1
    axioms = trace (showDoc axioms1 "axioms") axioms1         --  axioms
    _axioms = map quanti axioms
    l_Syms1 = map leadingSym axioms
    l_Syms = trace (showDoc l_Syms1 "leading_Symbol") l_Syms1
                                                      -- leading_Symbol
    spSrts = filter (\s->not $ elem s srts) nSorts
    notFreeSorts = filter (\s-> (fst $ isSubSort s oSorts axOfS) == False &&
                   (is_free_gen_sort s axOfS) == Just False) spSrts
    subSorts = filter (\s-> (fst $ isSubSort s oSorts axOfS) == True) spSrts
    subSortsF = map (\s->isSubSort s oSorts axOfS) subSorts
{-
   check all partial axiom
-}
    p_axioms = filter partialAxiom _axioms           -- all partial axioms
    ax_without_dom = filter (not.isDomain) _axioms
    t_axioms = filter (not.partialAxiom) _axioms     -- all total axioms
    un_p_axioms = filter (not.contain_Def) p_axioms
    dom_l1 = domainOpSymbs p_axioms
    dom_l = trace (showDoc dom_l1 "domain_list") dom_l1
    pcheck = filter (\f-> case quanti f of
                            Strong_equation t _ _ -> 
                              elem (opSymbOfTerm t) dom_l
                            Existl_equation t _ _ ->
                              elem (opSymbOfTerm t) dom_l
                            _ -> False) p_axioms
    impl_p_axioms = filter (\f-> case f of    -- del
                                   Equivalence _ _ _ -> False
                                   Negation _ _ -> False
                                   _ -> True) p_axioms
{-
  check if leading symbols are new (not in the image of morphism),
        if not, return Nothing
-}
    op_fs = filter (\f-> case leadingSym f of
                           Just (Left _) -> True
                           _ -> False) _axioms
    pred_fs = filter (\f-> case leadingSym f of
                             Just (Right _) -> True
                             _ -> False) _axioms
    id_ots = concat $ map filterOp $ l_Syms
    id_pts = concat $ map filterPred $ l_Syms
    old_op_id= idStr $ fst $ head $ filter (\ot->find_ot ot) $ id_ots
    old_pred_id = idStr $ fst $ head $ filter (\pt->find_pt pt) $ id_pts
    old_op_ps = case head $ map leading_Term_Predication $
                     filter (\f-> find_ot $ head $ filterOp $
                                  leadingSym f) op_fs of
                  Just (Left (Application _ _ p)) -> p
                  _ -> nullRange
    old_pred_ps = case head $ map leading_Term_Predication $
                       filter (\f->find_pt $ head $ filterPred $
                                   leadingSym f) pred_fs of
                    Just (Right (Predication _ _ p)) -> p
                    _ -> nullRange
    find_ot (ident,ot) = case Map.lookup ident oldOpMap of
                           Nothing -> False
                           Just ots -> Set.member ot ots
    find_pt (ident,pt) = case Map.lookup ident oldPredMap of
                           Nothing -> False
                           Just pts -> Set.member pt pts
{-
   the leading terms consist of variables and constructors only,
   if not, return Nothing
   - split function leading_Symb into
      leading_Term_Predication::FORMULA f -> Maybe(Either Term (Formula f))
       and
      extract_leading_symb::Either Term (Formula f) -> Either OP_SYMB PRED_SYMB
   - collect all operation symbols from
        recover_Sort_gen_ax fconstrs (= constructors)
  the leading predication consist of only variables and constructors too
-}
    ltp1 = map leading_Term_Predication _axioms
    ltp = trace (showDoc ltp1 "leading_term_pred") ltp1
                                     --  leading_term_pred
    leadingTerms1 = concat $ map (\tp->case tp of
                                         Just (Left t)->[t]
                                         _ -> []) $ ltp
    leadingTerms = trace (showDoc leadingTerms1 "leadingTerm") leadingTerms1
                                                               -- leading Term
    leadingPreds = concat $ map (\tp->case tp of
                                        Just (Right f)->[f]
                                        _ -> []) $ ltp
{-
   check that patterns do not overlap, if not, return Nothing This means:
       in each group of the grouped axioms:
       all patterns of leading terms/formulas are disjoint
       this means: either leading symbol is a variable,
                           and there is just one axiom
                   otherwise, group axioms according to leading symbol
                              no symbol may be a variable
                              check recursively the arguments of constructor
                              in each group
-}
    leadingSymPatterns =
        case (groupAxioms (t_axioms ++ impl_p_axioms)) of
          Just sym_fs ->
              zip (fst $ unzip sym_fs) $
              (map ((map (\f->case f of
                                Just (Left (Application _ ts _))->ts
                                Just (Right (Predication _ ts _))->ts
                                _ -> [])).
                    (map leading_Term_Predication)) $ map snd sym_fs)
          Nothing -> error "CASL.CCC.FreeTypes.<leadingSymPatterns>"
    overlapSym1 = map fst $
                  filter (\sp->not $ checkPatterns $ snd sp) leadingSymPatterns
    overlapSym = trace (showDoc overlapSym1 "OverlapSym") overlapSym1
    overlap_Axioms fos
        | length fos <= 1 = [[]]
        | length fos == 2 = if not $ checkPatterns $ map patternsOfAxiom fos
                            then [fos]
                            else [[]]
        | otherwise = (concat $ map overlap_Axioms $
                       map (\f->[(head fos),f]) $ (tail fos)) ++
                      (overlap_Axioms $ tail fos)
    overlapAxioms1 = filter (\p-> not $ null p) $
                     concat $ map overlap_Axioms $ map snd $
                     filter (\a-> (fst a) `elem` overlapSym) $
                     fromJust $ groupAxioms (t_axioms ++ impl_p_axioms)
    overlapAxioms = trace (showDoc overlapAxioms1 "OverlapA") overlapAxioms1
    numOfImpl fos = length $ filter is_impli fos
    overlapQuery fos =
        case (checkPatterns2 $ map patternsOfAxiom fos) of
          Just True -> error "overlapQuery:not overlap"
          Just False -> overlapQuery1 fos
          Nothing -> overlapQuery2 fos
    overlapQuery1 fos =
        case numOfImpl fos of
          0 -> False_atom nullRange
          1 -> Negation (head cond) nullRange
          _ -> Negation (Conjunction cond nullRange) nullRange
      where cond= nub $ concat $ map conditionAxiom fos
    overlapQuery2 fos =
        case numOfImpl fos of
          0 -> resQ
          1 -> Implication (head cond) resQ True nullRange
          _ -> Implication (Conjunction cond nullRange) resQ True nullRange
      where cond= nub $ concat $ map conditionAxiom fos
            res= concat $ map resultAxiom fos
            resQ
              | null res = Negation (Conjunction cond nullRange) nullRange
              | length res == 1 = Negation (head cond) nullRange
              | otherwise = Strong_equation (head res) (last res) nullRange
    overlap_query1 = map overlapQuery overlapAxioms
    overlap_query = trace (showDoc overlap_query1 "OverlapQ") overlap_query1
    pattern_Pos [] = error "pattern overlap"
    pattern_Pos sym_ps =
        if not $ checkPatterns $ snd $ head sym_ps then symPos $ fst $
                                                        head sym_ps
        else pattern_Pos $ tail sym_ps
    symPos sym = case sym of
                   Left (Qual_op_name on _ ps) -> (idStr on,ps)
                   Right (Qual_pred_name pn _ ps) -> (idStr pn,ps)
                   _ -> error "pattern overlap"
    ex_axioms = filter is_ex_quanti $
                map sentence (filter is_user_or_sort_gen (osens ++ fsn))
    -- proof = terminationProof (osens ++ fsn)
    proof = terminationProof fsn


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
                    else [(fp,snd $ unzip $ filter (\x->(fst x)==fp) (p:ps))]
                symb'= if not $ (elem fp symb) then fp:symb
                       else symb
            in p'++(filterA ps symb')


isSubSort :: SORT -> [SORT] -> [FORMULA f] -> (Bool,[FORMULA f])
isSubSort _ _ [] = (False,[])
isSubSort s sts (f:fs) =
    case f of
      Quantification Universal [vd] f1 _ ->
          if elem (sortOfVar_Decl vd) sts
          then case f1 of
                 Equivalence (Membership _ s1 _) f2 _ ->
                     if s1==s
                     then (True,
                           [(Quantification Existential [vd] f2 nullRange)])
                     else isSubSort s sts fs
                 _ -> isSubSort s sts fs
          else isSubSort s sts fs
      _ -> isSubSort s sts fs


sortOfVar_Decl :: VAR_DECL -> SORT
sortOfVar_Decl (Var_decl _ s _) = s


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
        checkT (Simple_id _) = True 
        checkT (Qual_var _ _ _) = True
        checkT (Application subop subts _) = 
            (isCons sig cons subop) &&
            (all checkT subts)
        checkT _ = False



-- |  no variable occurs twice in a leading term,
--      if not, return Nothing

checkVar_App :: (Eq f) => TERM f -> Bool
checkVar_App (Application _ ts _) = notOverlap $ concat $ map varOfTerm ts
checkVar_App _ = error "CASL.CCC.FreeTypes<checkVar_App>"


allIdentic :: (Eq a) => [a] -> Bool
allIdentic ts = all (\t-> t== (head ts)) ts


notOverlap :: (Eq a) => [a] -> Bool
notOverlap [] = True
notOverlap (p:ps) = if elem p ps then False
                    else notOverlap ps


patternsOfTerm :: TERM f -> [TERM f]
patternsOfTerm t = case t of
                     Qual_var _ _ _ -> [t]
                     Application (Qual_op_name _ _ _) ts _-> ts
                     Sorted_term t' _ _ -> patternsOfTerm t'
                     Cast t' _ _ -> patternsOfTerm t'
                     _ -> []


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


sameOps_App :: TERM f -> TERM f -> Bool
sameOps_App app1 app2 = case (term app1) of               -- eq of app
                          Application ops1 _ _ ->
                              case (term app2) of
                                Application ops2 _ _ -> ops1==ops2
                                _ -> False
                          _ -> False


group_App :: [[TERM f]] -> [[[TERM f]]]
group_App [] = []
group_App ps = (filter (\p1-> sameOps_App (head p1) (head (head ps))) ps):
               (group_App $ filter (\p2-> not $
                                   sameOps_App (head p2) (head (head ps))) ps)


-- | it examines whether it is overlap
checkPatterns :: (Eq f) => [[TERM f]] -> Bool
checkPatterns ps
        | length ps <=1 = True
        | allIdentic ps = False
        | all isVar $ map head ps =
            if allIdentic $ map head ps then checkPatterns $ map tail ps
            else False
        | all (\p-> sameOps_App p (head (head ps))) $ map head ps =
            checkPatterns $ map (\p'->(patternsOfTerm $ head p')++(tail p')) ps
        | all isApp $ map head ps = all id $ map checkPatterns $ group_App ps
        | otherwise = False


checkPatterns2 :: (Eq f) => [[TERM f]] -> Maybe Bool
checkPatterns2 ps
        | length ps <=1 = Just True
        | allIdentic ps = Nothing
        | all isVar $ map head ps =
            if allIdentic $ map head ps then checkPatterns2 $ map tail ps
            else Just False
        | all (\p-> sameOps_App p (head (head ps))) $ map head ps =
            checkPatterns2 $
            map (\p'->(patternsOfTerm $ head p')++(tail p')) ps
        | all isApp $ map head ps = Nothing
        | otherwise = Just False


conditionAxiom ::  FORMULA f -> [ FORMULA f]
conditionAxiom f = case f of
                     Quantification _ _ f' _ -> conditionAxiom f'
                     Implication f' _ _ _ -> [f']
                     Equivalence _ f' _ -> [f']
                     _ -> []


resultAxiom :: FORMULA f -> [TERM f]
resultAxiom f = case f of
                  Quantification _ _ f' _ -> resultAxiom f'
                  Implication _ f' _ _ -> resultAxiom f'
                  Negation f' _ -> resultAxiom f'
                  Strong_equation _ t _ -> [t]
                  Existl_equation _ t _ -> [t]
                  _ -> []


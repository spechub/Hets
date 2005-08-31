{- | 

    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
    License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

-}

{-  
"free datatypes and recursive equations are consistent"

checkFreeType :: (PrettyPrint f, Eq f) => 
                 (Sign f e,[Named (FORMULA f)]) -> Morphism f e m 
                 -> [Named (FORMULA f)] -> Result (Maybe Bool)
Just (Just True) => Yes, is consistent
Just (Just False) => No, is inconsistent
Just Nothing => don't know
-}


module CASL.CCC.FreeTypes where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import CASL.CCC.SignFuns
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof
import Common.AS_Annotation
import Common.PrettyPrint
import Common.Result
import Common.Id
import Maybe
-- import System.Cmd
-- import System.IO.Unsafe
import Debug.Trace

{-
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
  - return (Just True)
-}
checkFreeType :: (PosItem f, PrettyPrint f, Eq f) => 
                 (Sign f e,[Named (FORMULA f)]) -> Morphism f e m 
                 -> [Named (FORMULA f)] -> Result (Maybe (Bool,[FORMULA f]))
checkFreeType (osig,osens) m fsn      
    | any (\s->not $ elem s srts) newL =
        let (Id ts _ pos) = head $ filter (\s->not $ elem s srts) newL
            sname = concat $ map tokStr ts 
	in warning Nothing (sname ++ " is not freely generated") pos
    | any (\s->not $ elem s f_Inhabited) newL =
        let (Id ts _ pos) = head $ filter (\s->not $ elem s f_Inhabited) newL
            sname = concat $ map tokStr ts 
        in warning (Just (False,[])) (sname ++ " is not inhabited") pos
    | elem Nothing l_Syms =
        let pos = snd $ head $ filter (\f'-> (fst f') == Nothing) $ 
		  map leadingSymPos _axioms
        in warning Nothing "axiom is not definitional" pos
    | not $ null $ p_t_axioms ++ pcheck = 
	let pos = posOf (p_t_axioms ++ pcheck)
        in warning Nothing "partial axiom is not definitional" pos
    | any id $ map find_ot id_ots =    
        let pos = old_op_ps
        in warning Nothing ("Op: " ++ old_op_id ++ " is not new") pos
    | any id $ map find_pt id_pts =
        let pos = old_pred_ps
        in warning Nothing ("Predication: " ++old_pred_id++ " is not new") pos
    | not $ and $ map checkTerm leadingTerms =
        let (Application os _ pos) = 
		head $ filter (\t->not $ checkTerm t) leadingTerms
        in warning Nothing ("a leading term of " ++ (opSymStr os) ++
           " consist of not only variables and constructors") pos
    | not $ and $ map checkVar leadingTerms =
        let (Application os _ pos) = 
		head $ filter (\t->not $ checkVar t) leadingTerms
        in warning Nothing ("a variable occurs twice in a leading term of " ++
			    opSymStr os) pos
--    | not $ and $ map checkPatterns leadingPatterns = 
--        let (symb, pos) = pattern_Pos leadingSymPatterns  
--        in warning Nothing ("patterns overlap in " ++ symb) pos
--    | (not $ null (axioms ++ old_axioms)) && (not $ proof) = 
    | terminationProof (osens ++ fsn) =
	warning Nothing "not terminating" nullRange
    | not $ null overlap_query = 
  --  | not $ null overlapSym = 
        return (Just (True,overlap_query))
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
    fs = trace (showPretty fs1 "new formulars") fs1     -- new formulars
--    is_user_or_sort_gen ax = take 12 name == "ga_generated" || 
--			     take 3 name /= "ga_"
--             where name = senName ax
    sig = imageOfMorphism m
    oldSorts1 = Set.union (sortSet sig) (sortSet osig)
    oldSorts = trace (showPretty oldSorts1 "old sorts") oldSorts1  -- old sorts
    allSorts1 = sortSet $ mtarget m
    allSorts = trace (showPretty allSorts1 "all sorts") allSorts1
    newSorts1 = Set.filter (\s-> not $ Set.member s oldSorts) allSorts
                                                          -- new sorts
    newSorts = trace (showPretty newSorts1 "new sorts") newSorts1
    newL = Set.toList newSorts
    oldOpMap = opMap sig
    oldPredMap = predMap sig 
    fconstrs = concat $ map constraintOfAxiom fs
 --   fc f = case f of
 --            Sort_gen_ax constrs True -> constrs
 --            _ ->[]
    (srts1,constructors1,_) = recover_Sort_gen_ax fconstrs
    srts = trace (showPretty srts1 "srts") srts1      --   srts
    constructors = trace (showPretty constructors1 "constrs") constructors1   
                                                           -- constructors
    f_Inhabited1 = inhabited (Set.toList oldSorts) fconstrs
    f_Inhabited = trace (showPretty f_Inhabited1 "f_inhabited" ) f_Inhabited1 
                                                             --  f_inhabited
    axioms1 = filter (\f-> case f of                       
                             Sort_gen_ax _ _ -> False
                             _ -> True) fs
    axioms = trace (showPretty axioms1 "axioms") axioms1         --  axioms
    _axioms = map (\f-> case f of
                          Quantification _ _ f' _ -> f'
                          _ -> f) axioms
    l_Syms1 = map leadingSym axioms                                    
    l_Syms = trace (showPretty l_Syms1 "leading_Symbol") l_Syms1  
                                                      -- leading_Symbol
    op_Syms = concat $ map (\s-> case s of
                                   Just (Left op) -> [op]
                                   _ -> []) l_Syms
--    pred_Syms1 = concat $ map (\s-> case s of
--                                     Just (Right p) -> [p]
--                                     _ -> []) l_Syms
--    pred_Syms = trace (showPretty pred_Syms1 "PRED_SYM") pred_Syms1
  
{-
  check all partial axiom
-}
    p_axioms = filter partialAxiom _axioms           -- all partial axioms
    t_axioms = filter (not.partialAxiom) _axioms     -- all total axioms 
    p_t_axioms = filter (\f-> case (opTyp_Axiom f) of            
                      -- exist partial axioms in total axioms?
                                Just False -> True
                                _ -> False) t_axioms
    equi_p_axioms = filter (\f-> case f of
                                   Equivalence _ _ _ -> True
                                   _ -> False) p_axioms
    opSyms_p = map (\os-> case os of
                            (Just (Left opS)) -> opS
                            _ -> error "CASL.CCC.FreeTypes.<partial axiom>") $
               map leadingSym equi_p_axioms 
    impl_p_axioms = filter (\f-> case f of
                                   Equivalence _ _ _ -> False
                                   Negation _ _ -> False
                                   _ -> True) p_axioms
    pcheck = foldl (\im os-> filter (\im'-> 
				     case leadingSym im' of
                                       (Just (Left opS)) -> opS /= os
                                       _ -> False) im) impl_p_axioms opSyms_p
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
    filterOp symb = case symb of
                      Just (Left (Qual_op_name ident (Op_type k as rs _) _))->
			  [(ident, OpType {opKind=k, opArgs=as, opRes=rs})]
                      _ -> []
    filterPred symb = case symb of
                        Just (Right (Qual_pred_name ident (Pred_type s _) _))->
                            [(ident, PredType {predArgs=s})]
                        _ -> [] 
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
-}
    ltp1 = map leading_Term_Predication (t_axioms ++ impl_p_axioms)
    ltp = trace (showPretty ltp1 "leading_term_pred") ltp1
                                     --  leading_term_pred
    leadingTerms1 = concat $ map (\tp->case tp of
                                         Just (Left t)->[t]
                                         _ -> []) $ ltp
    leadingTerms = trace (showPretty leadingTerms1 "leadingTerm") leadingTerms1
                                                               -- leading Term
    checkTerm (Sorted_term t _ _) = checkTerm t
    checkTerm (Qual_var _ _ _) = True
    checkTerm (Application _ ts _)= 
	let checkT (Sorted_term t _ _) = checkTerm t
            checkT (Qual_var _ _ _) = True
            checkT (Application subop subts _) = (elem subop constructors) &&
                                                 (all id $ map checkT subts)  
	    checkT _ = False
        in all id $ map checkT ts
    checkTerm _ = error "CASL.CCC.FreeTypes.<checkTerm>"
{-
   no variable occurs twice in a leading term, 
      if not, return Nothing
-} 
    checkVar (Application _ ts _) = notOverlap $ concat $ map allVarOfTerm ts
    checkVar _ = error "CASL.CCC.FreeTypes<checkVar>"
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
          Nothing -> error "CASL.CCC.FreeTypes.<axiom group>"
--    leadingPatterns1 = snd $ unzip leadingSymPatterns           -- *
--    leadingPatterns = 
--	trace (showPretty leadingPatterns1 "leadingPatterns") leadingPatterns1
                                                            --leading Patterns
    isApp t = case t of
                Application _ _ _->True
                Sorted_term t' _ _ ->isApp t'
                _ -> False
    isVar t = case t of
                Qual_var _ _ _ ->True
                Sorted_term t' _ _ ->isVar t'
                _ -> False
    allIdentic ts = all (\t-> t== (head ts)) ts
    notOverlap ts = let check [] = True
                        check (p:ps)=if elem p ps then False
                                     else check ps
                    in check ts 
    patternsOfTerm t = case t of
                         Qual_var _ _ _ -> [t]
                         Application (Qual_op_name _ _ _) ts _-> ts
                         Sorted_term t' _ _ -> patternsOfTerm t'
                         Cast t' _ _ -> patternsOfTerm t'
                         _ -> []
    patternsOfAxiom f = case f of
                          Quantification _ _ f' _ -> patternsOfAxiom f'
                          Negation f' _ -> patternsOfAxiom f'
                          Implication _ f' _ _ -> patternsOfAxiom f'
                          Equivalence f' _ _ -> patternsOfAxiom f'
                          Predication _ ts _ -> ts 
	                  Existl_equation t _ _ -> patternsOfTerm t
	                  Strong_equation t _ _ -> patternsOfTerm t
                          _ -> []
    sameOps app1 app2 = case (term app1) of               -- eq of app
                          Application ops1 _ _ -> 
			      case (term app2) of
                                Application ops2 _ _ -> ops1==ops2
                                _ -> False
                          _ -> False
    group [] = []
    group ps = (filter (\p1-> sameOps (head p1) (head (head ps))) ps):
               (group $ filter (\p2-> not $ 
                                      sameOps (head p2) (head (head ps))) ps)
    checkPatterns ps 
        | length ps <=1 = True
        | allIdentic ps = False
        | all isVar $ map head ps = 
	    if allIdentic $ map head ps then checkPatterns $ map tail ps
            else False
        | all (\p-> sameOps p (head (head ps))) $ map head ps = 
            checkPatterns $ map (\p'->(patternsOfTerm $ head p')++(tail p')) ps
        | all isApp $ map head ps = all id $ map checkPatterns $ group ps
        | otherwise = False
    checkPatterns2 ps 
        | length ps <=1 = Just True
        | allIdentic ps = Nothing
        | all isVar $ map head ps = 
	    if allIdentic $ map head ps then checkPatterns2 $ map tail ps
            else Just False
        | all (\p-> sameOps p (head (head ps))) $ map head ps = 
            checkPatterns2 $ 
            map (\p'->(patternsOfTerm $ head p')++(tail p')) ps
        | all isApp $ map head ps = Nothing
        | otherwise = Just False
    overlapSym1 = map fst $ 
                  filter (\sp->not $ checkPatterns $ snd sp) leadingSymPatterns
    overlapSym = trace (showPretty overlapSym1 "OverlapSym") overlapSym1 
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
    overlapAxioms = trace (showPretty overlapAxioms1 "OverlapA") overlapAxioms1
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
      where cond= everyOnce $ concat $ map conditionAxiom fos
    overlapQuery2 fos = 
        case numOfImpl fos of
          0 -> resQ
          1 -> Implication (head cond) resQ True nullRange
          _ -> Implication (Conjunction cond nullRange) resQ True nullRange
      where cond= everyOnce $ concat $ map conditionAxiom fos
            res= concat $ map resultAxiom fos
            resQ = Strong_equation (head res) (last res) nullRange
    conditionAxiom f = case f of
                         Quantification _ _ f' _ -> conditionAxiom f'
                         Implication f' _ _ _ -> [f']
                         _ -> []
    resultAxiom f = case f of
                      Quantification _ _ f' _ -> resultAxiom f'
                      Implication _ f' _ _ -> resultAxiom f'
                      Negation f' _ -> resultAxiom f'
                      Strong_equation _ t _ -> [t]
                      Existl_equation _ t _ -> [t]
                      _ -> []
    overlap_query1 = map overlapQuery overlapAxioms
    overlap_query = trace (showPretty overlap_query1 "OverlapQ") overlap_query1
    pattern_Pos [] = error "pattern overlap"
    pattern_Pos sym_ps = 
	if not $ checkPatterns $ snd $ head sym_ps then symPos $ fst $ 
                                                        head sym_ps
	else pattern_Pos $ tail sym_ps
    symPos sym = case sym of
                   Left (Qual_op_name on _ ps) -> (idStr on,ps)
                   Right (Qual_pred_name pn _ ps) -> (idStr pn,ps)
                   _ -> error "pattern overlap"
{- 
   Automatic termination proof
   using cime, see http://cime.lri.fr/

  interface to cime system, using system
  transform CASL signature to Cime signature, 
  CASL formulas to Cime rewrite rules

Example1:

spec NatJT2 = {} then
  free type Nat ::= 0 | suc(Nat)
  op __+__ : Nat*Nat->Nat
  forall x,y:Nat
  . 0+x=x
  . suc(x)+y=suc(x+y)
end

theory generated by Hets:

sorts Nat
op 0 : Nat
op __+__ : Nat * Nat -> Nat
op suc : Nat -> Nat

forall X1:Nat; Y1:Nat
    . (op suc : Nat -> Nat)((var X1 : Nat) : Nat) : Nat =
          (op suc : Nat -> Nat)((var Y1 : Nat) : Nat) : Nat <=>
          (var X1 : Nat) : Nat = (var Y1 : Nat) : Nat %(ga_injective_suc)%

forall Y1:Nat
    . not (op 0 : Nat) : Nat =
        (op suc : Nat -> Nat)((var Y1 : Nat) : Nat) : Nat %(ga_disjoint_0_suc)%

generated{sort Nat; op 0 : Nat;
                    op suc : Nat -> Nat} %(ga_generated_Nat)%

forall x, y:Nat
    . (op __+__ : Nat * Nat -> Nat)((op 0 : Nat) : Nat,
                                    (var x : Nat) : Nat) : Nat =
          (var x : Nat) : Nat

forall x, y:Nat
    . (op __+__ : Nat *
                  Nat -> Nat)((op suc : Nat -> Nat)((var x : Nat) : Nat) : Nat,
                              (var y : Nat) : Nat) : Nat =
          (op suc : Nat -> Nat)((op __+__ : Nat *
                                            Nat -> Nat)((var x : Nat) : Nat,
                                                        (var y : Nat) : Nat) :
                                                                    Nat) : Nat

CiME:
let F = signature "when_else : 3; 
                   eq : binary;
                   and : binary;
                   or : binary; 
                   not: unary; 
                   True,False : constant; 
                   0 : constant; 
                   suc : unary; 
                   __+__ : binary; ";
let X = vars "t1 t2 x y";
let axioms = TRS F X "
eq(t1,t1) -> True; 
eq(t1,t2) -> False;
and(True,True) -> True; 
and(True,False) -> False; 
and(False,True) -> False; 
and(False,False) -> False;
or(True,True) -> True; 
or(True,False) -> True; 
or(False,True) -> True; 
or(False,False) -> False;
not(True) -> False;
not(False) -> True; 
when_else(t1,True,t2) -> t1; 
when_else(t1,False,t2) -> t2; 
__+__(0,x) -> x; 
__+__(suc(x),y) -> suc(__+__(x,y)); ";
termcrit "dp";
termination axioms;

Example2:
spec NatJT1 = 
  sort Elem
  free type Bool ::= True | False
  op __or__ : Bool*Bool->Bool
  . True or True = True
  . True or False = True
  . False or True = True
  . False or False = False
then
  free types Tree ::= Leaf(Elem) | Branch(Forest);
             Forest ::= Nil | Cons(Tree;Forest)
  op elemT : Elem * Tree -> Bool
  op elemF : Elem * Forest -> Bool
  forall x,y:Elem; t:Tree; f:Forest
  . elemT(x,Leaf(y)) = True when x=y else False
  . elemT(x,Branch(f)) = elemF(x,f)
  . elemF(x,Nil) = False
  . elemF(x,Cons(t,f)) = elemT(x,t) or elemF(x,f)
end

CiME:
let F = signature "when_else : 3; 
                   eq : binary;
                   and : binary;
                   or : binary;
                   not : unary; 
                   True,False : constant; 
                   True : constant; 
                   False : constant; 
                   __or__ : binary; 
                   Leaf : unary; 
                   Branch : unary; 
                   Nil : constant; 
                   Cons : binary; 
                   elemT : binary; 
                   elemF : binary; ";
let X = vars "t1 t2 x y t f";
let axioms = TRS F X "
eq(t1,t1) -> True;
eq(t1,t2) -> False;
and(True,True) -> True; 
and(True,False) -> False; 
and(False,True) -> False; 
and(False,False) -> False;
or(True,True) -> True; 
or(True,False) -> True; 
or(False,True) -> True; 
or(False,False) -> False;
not(True) -> False;
not(False) -> True;
when_else(t1,True,t2) -> t1;
when_else(t1,False,t2) -> t2;
__or__(True,True) -> True; 
__or__(True,False) -> True; 
__or__(False,True) -> True; 
__or__(False,False) -> False;
elemT(x,Leaf(y)) -> when_else(True,eq(x,y),False); 
elemT(x,Branch(f)) -> elemF(x,f); 
elemF(x,Nil) -> False; 
elemF(x,Cons(t,f)) -> __or__(elemT(x,t),elemF(x,f)); ";

------------------------------------------------------------------------
--    oldfs1 = map sentence (filter is_user_or_sort_gen osens)
--    oldfs = trace (showPretty oldfs1 "old formulas") oldfs1   -- old formulas
--    old_axioms = filter (\f->case f of                      
--                               Sort_gen_ax _ _ -> False
--                               _ -> True) oldfs
--    all_axioms = old_axioms ++ axioms
    all_predSymbs = everyOnce $ concat $ map predSymbsOfAxiom all_axioms
    o_fconstrs = concat $ map constraintOfAxiom oldfs
    (_,o_constructors1,_) = recover_Sort_gen_ax o_fconstrs
    o_constructors = trace (showPretty o_constructors1 "Ocons") o_constructors1
                                                           -- old constructors
    o_l_Syms1 = map leadingSym $ filter isOp_Pred $ oldfs             
    o_l_Syms = trace (showPretty o_l_Syms1 "o_leading_Symbol") o_l_Syms1
                                                          -- old leading_Symbol
    o_op_Syms = concat $ map (\s-> case s of
                                     Just (Left op) -> [op]
                                     _ -> []) o_l_Syms
--    o_pred_Syms1 = concat $ map (\s-> case s of
--                                       Just (Right p) -> [p]
--                                       _ -> []) o_l_Syms
--    o_pred_Syms = trace (showPretty o_pred_Syms1 "OLD_PRED_SYM") o_pred_Syms1

    --  build signature of operation together 
    opSignStr signs str                      
        | null signs = str
        | otherwise = opSignStr (tail signs) (str ++ 
					      (opS_cime $ head signs) ++ ";\n")
    --  build signature of predication together 
    predSignStr signs str                      
        | null signs = str
        | otherwise = 
	    predSignStr (tail signs) (str ++ 
				      (predS_cime $ head signs) ++ ";\n")
    allVar vs = everyOnce $ concat vs
--	foldl (\hv tv->hv ++ 
--	               (filter (\v->not $ elem v hv) tv)) (head vs) (tail vs)
    --  transform variables to string
    varsStr vars str                               
        | null vars = str
        | otherwise = if null str then varsStr (tail vars) (tokStr $ head vars)
                      else varsStr (tail vars) (str ++ " " ++ 
						(tokStr $ head vars))
    --  transform all axioms to string
    axiomStr axs str
        | null axs = str
        | otherwise = 
	    axiomStr (tail axs) (str ++ (axiom_cime $ (head axs)) ++ ";\n")
    impli_equiv = filter is_impli_equiv all_axioms
    n_impli_equiv = filter (not.is_impli_equiv) all_axioms
    sighead = "let F = signature \"when_else : 3;\n" ++
                                  "eq : binary;\n" ++
                                  "and : binary;\n" ++
                                  "or : binary;\n" ++
                                  "not : unary;\n" ++ 
                                  "True,False : constant;\n"
    auxSigstr ies i str 
        | null ies = str
        | otherwise =  
              auxSigstr (tail ies) (snd $ last tmp) (str ++ 
                             (concat $ map (\s-> ((fst.fst) s) ++ 
                             (dimension $ ((snd.fst) s)) ++ ";\n") tmp))
            where tmp = sigAuxf (head ies) i
    sigAux = auxSigstr impli_equiv 1 ""
    auxAxstr afs i str
        | null afs = str
        | otherwise =
              auxAxstr (tail afs) (snd tmp) (str ++ (fst tmp))
            where tmp = impli_equiv_cime i (head afs)
    axAux = auxAxstr impli_equiv 1 ""  
    varhead = "let X = vars \"t1 t2 "
    axhead = "let axioms = TRS F X \"eq(t1,t1) -> True;\n" ++ 
                                    "eq(t1,t2) -> False;\n" ++
                                    "and(True,True) -> True;\n" ++
                                    "and(True,False) -> False;\n" ++
                                    "and(False,True) -> False;\n" ++
                                    "and(False,False) -> False;\n" ++
                                    "or(True,True) -> True;\n" ++
                                    "or(True,False) -> True;\n" ++
                                    "or(False,True) -> True;\n" ++
                                    "or(False,False) -> False;\n" ++
                                    "not(True) -> False;\n" ++
                                    "not(False) -> True;\n" ++  
                                    "when_else(t1,True,t2) -> t1;\n" ++ 
                                    "when_else(t1,False,t2) -> t2;\n"
    c_sigs = (sighead ++ (opSignStr (everyOnce (o_constructors ++ 
					       constructors ++ 
					       o_op_Syms ++ 
					       op_Syms)) "") ++
			 (predSignStr all_predSymbs "") ++
	      sigAux ++ "\";\n")
    c_vars = (varhead ++ (varsStr (allVar $ map varOfAxiom $ 
			           all_axioms) "") ++ "\"; \n")
    c_axms = if null n_impli_equiv 
             then (axhead ++ axAux ++ "\";\n")
             else (axhead ++ (axiomStr n_impli_equiv "") ++ axAux ++ "\";\n")
    ipath = "/tmp/Input.cime"
    opath = "/tmp/Result.cime"
    c_proof = ("termcrit \"dp\";\n" ++
               "termination axioms;\n" ++
               "#quit;")  
    proof = 
	unsafePerformIO (do
            writeFile ipath (c_sigs ++ c_vars ++ c_axms ++ c_proof)
            system ("cime < " ++ ipath ++ " | cat > " ++ opath)
            res <- readFile opath
            -- system ("rm ./CASL/CCC/*.cime")
            return (subStr "Termination proof found." res))
-}


{- group the axioms according to their leading symbol
   output Nothing if there is some axiom in incorrect form -}
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



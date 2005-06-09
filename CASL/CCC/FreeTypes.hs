{-# OPTIONS -cpp #-}
{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

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

{- todo

Improve warnings: sort s should output the actual sort
                  more informative messages
Document the code

Check CASL-lib/Basic/Numbers.casl

-} 

module CASL.CCC.FreeTypes where

import Debug.Trace
import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
-- import qualified Common.Lib.Rel as Rel
import CASL.CCC.SignFuns
import Common.AS_Annotation
import Common.PrettyPrint
-- import Common.Lib.Pretty
import Common.Result
import Common.Id
#ifdef UNI_PACKAGE
-- import Isabelle.IsaProve
import ChildProcess
#endif
import Foreign

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
                 -> [Named (FORMULA f)] -> Result (Maybe Bool)
checkFreeType (osig,osens) m fsn      
#ifdef UNI_PACKAGE
    | any (\s->not $ elem s srts) newL =
        let (Id ts _ pos) = head $ filter (\s->not $ elem s srts) newL
            sname = concat $ map tokStr ts 
	in warning Nothing (sname ++ " is not freely generated") pos
    | any (\s->not $ elem s f_Inhabited) newL =
        let (Id ts _ pos) = head $ filter (\s->not $ elem s f_Inhabited) newL
            sname = concat $ map tokStr ts 
        in warning (Just False) (sname ++ " is not inhabited") pos
    | elem Nothing l_Syms =
        let pos = snd $ head $ filter (\f'-> (fst f') == Nothing) $ 
		  map leadingSymPos _axioms
        in warning Nothing "axiom is not definitional" pos
    | not $ null $ p_t_axioms ++ pcheck = 
	let pos = posOf (p_t_axioms ++ pcheck)
        in warning Nothing "partial axiom is not definitional" pos
    | any id $ map find_ot id_ots =    
        let pos = old_op_ps
        in warning Nothing ("Op: " ++ old_op_id ++ " ist not new") pos
    | any id $ map find_pt id_pts =
        let pos = old_pred_ps
        in warning Nothing ("Pedication: " ++ old_pred_id ++ " ist not new")pos
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
    | not $ and $ map checkPatterns leadingPatterns = 
        let (symb, pos) = pattern_Pos leadingSymPatterns
        in warning Nothing ("patterns overlap in " ++ symb) pos
    | (not $ null (axioms ++ old_axioms)) && (not $ proof) = 
	warning Nothing "not terminating" []
#endif         
    | otherwise = return (Just True)
#ifdef UNI_PACKAGE
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
    is_user_or_sort_gen ax = take 12 name == "ga_generated" || 
			     take 3 name /= "ga_"
             where name = senName ax
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
    fconstrs = concat $ map fc fs
    fc f = case f of
             Sort_gen_ax constrs True -> constrs
             _ ->[]
    (srts1,constructors1,_) = recover_Sort_gen_ax fconstrs
    srts = trace (showPretty srts1 "srts") srts1      --   srts
    constructors = trace (showPretty constructors1 "constrs") constructors1   
                                                           -- constructors
    f_Inhabited1 = inhabited (Set.toList oldSorts) fconstrs
    f_Inhabited = trace (showPretty f_Inhabited1 "f_inhabited" ) f_Inhabited1 
                                                             --  f_inhabited
--  leading_o_p1 = filter isOp_Pred fs
--  leading_o_p = trace (showPretty leading_o_p1 "leading_o_p") leading_o_p1
                                                             -- leading_o_p
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
    pred_Syms = concat $ map (\s-> case s of
                                     Just (Right p) -> [p]
                                     _ -> []) l_Syms  
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
                  _ -> []
    old_pred_ps = case head $ map leading_Term_Predication $ 
                       filter (\f->find_pt $ head $ filterPred $ 
                                   leadingSym f) pred_fs of
                    Just (Right (Predication _ _ p)) -> p
                    _ -> []
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
   --   if not (elem subop constructors) then error (showPretty subop "warum?")
   -- &&
   --   else True
                                                 (all id $ map checkT subts)  
	    checkT _ = False
        in all id $ map checkT ts
   --  all id $ map (\t-> case (term t) of
   --             Qual_var _ _ _ -> True
   --             Application subOp subTs _ ->(elem subOp constructors) &&
   --                                         (all id $ map checkTerm (subTs))
   --             _ -> False) ts
    checkTerm _ = error "CASL.CCC.FreeTypes.<checkTerm>"
{-
   no variable occurs twice in a leading term, 
      if not, return Nothing
-} 
    checkVar (Application _ ts _) = notOverlap $ concat $ map allVarOfTerm ts
    checkVar _ = error "CASL.CCC.FreeTypes<checkVar>"
    allVarOfTerm t = case t of
                       Qual_var _ _ _ -> [t]
                       Sorted_term t' _ _ -> allVarOfTerm  t'
                       Application _ ts _ -> if length ts==0 then []
                                             else concat $ map allVarOfTerm ts
                       _ -> [] 
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
    leadingPatterns1 = snd $ unzip leadingSymPatterns
   --leadingPatterns = trace (showPretty leadingPatterns1 (tmp ++ "\n" ++ tmp1 ++ "\n" ++ tmp2 ++ "\n")) leadingPatterns1    --leading Patterns
    leadingPatterns = 
	trace (showPretty leadingPatterns1 "leadingPatterns") leadingPatterns1
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
                         Application (Qual_op_name _ _ _) ts _-> ts
                         Sorted_term t' _ _ -> patternsOfTerm t'
                         _ -> []
    sameOps app1 app2 = case (term app1) of
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

  interface to cime system, using newChildProcess
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
                   not: unary; 
                   True,False : constant; 
                   0 : constant; 
                   suc : unary; 
                   __+__ : binary; ";
let X = vars "t1 t2 x y";
let axioms = TRS F X "
eq(t1,t1) -> True; 
eq(t1,t2) -> False;
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

-}
    oldfs1 = map sentence (filter is_user_or_sort_gen osens)
    oldfs = trace (showPretty oldfs1 "old formulas") oldfs1   -- old formulas
    old_axioms = filter (\f->case f of                      
                               Sort_gen_ax _ _ -> False
                               _ -> True) oldfs
    o_fconstrs = concat $ map fc oldfs
    (_,o_constructors1,_) = recover_Sort_gen_ax o_fconstrs
    o_constructors = trace (showPretty o_constructors1 "Ocons") o_constructors1
                                                           -- old constructors
    o_l_Syms1 = map leadingSym $ filter isOp_Pred $ oldfs             
    o_l_Syms = trace (showPretty o_l_Syms1 "o_leading_Symbol") o_l_Syms1
                                                          -- old leading_Symbol
    o_op_Syms = concat $ map (\s-> case s of
                                     Just (Left op) -> [op]
                                     _ -> []) o_l_Syms
    o_pred_Syms = concat $ map (\s-> case s of
                                       Just (Right p) -> [p]
                                       _ -> []) o_l_Syms  
    --  read the result of proof
    rP cp = do
	    msg <- readMsg cp
            case msg of
              "Termination proof found." -> return True
              "Quitting." -> return False
              _ -> rP cp
    noDouble [] = []
    noDouble (x:xs) 
        | elem x xs = noDouble xs
        | otherwise = x:(noDouble xs)
    --  build signature of operation together 
    opSignStr signs str                      
        | null signs = str
        | otherwise = opSignStr (tail signs) (str ++ 
					      (opS_cime $ head signs) ++ "; ")
    --  build signature of predication together 
    predSignStr signs str                      
        | null signs = str
        | otherwise = 
	    predSignStr (tail signs) (str ++ 
				      (predS_cime $ head signs) ++ "; ")
    allVar vs = 
	foldl (\hv tv->hv ++ 
	               (filter (\v->not $ elem v hv) tv)) (head vs) (tail vs)
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
	    axiomStr (tail axs) (str ++ (axiom_cime $ (head axs)) ++ "; ")
    sighead = "let F = signature \"when_else : 3; " ++
                                  "eq : binary; " ++ 
                                  "not : unary ; " ++ 
                                  "True,False : constant; "
    varhead = "let X = vars \"t1 t2 "
    axhead = "let axioms = TRS F X \"eq(t1,t1) -> True; " ++ 
                                    "eq(t1,t2) -> False; " ++ 
                                    "not(True) -> False; " ++
                                    "not(False) -> True; " ++  
                                    "when_else(t1,True,t2) -> t1; " ++ 
                                    "when_else(t1,False,t2) -> t2; "
    proof = 
	unsafePerformIO (do
	--    cim <- newChildProcess "/home/xinga/bin/cime" []
            cim <- newChildProcess "cime" []
	    sendMsg cim (sighead ++ (opSignStr (noDouble (o_constructors ++ 
							    constructors ++ 
							    o_op_Syms ++ 
							    op_Syms)) "") ++
			 (predSignStr (noDouble (o_pred_Syms ++ 
						 pred_Syms)) "")++
			 "\";")
	    sendMsg cim (varhead ++ (varsStr (allVar $ map varOfAxiom $ 
					      old_axioms ++ axioms) "") ++ 
			 "\";")        
	    sendMsg cim (axhead ++
                         (axiomStr (old_axioms ++ axioms) "") ++
			 "\";")    
	    sendMsg cim "termcrit \"dp\";"
	    sendMsg cim "termination axioms;"
            sendMsg cim "#quit;"
            res <-rP cim
            return res)
{-
   --  print infomation 
         tmp  = ("let F = signature \"when_else : 3; eq : binary; True,False : constant; " ++ 
                              (opSignStr (noDouble (o_constructors ++ constructors ++ o_op_Syms ++ op_Syms)) "") ++
                              (predSignStr (noDouble (o_pred_Syms ++ pred_Syms)) "") ++ "\";") 
         tmp1 = ("let X = vars \"t1 t2 " ++ (varsStr (allVar $ map varOfAxiom $ old_axioms ++ axioms) "") ++ "\";")        
         tmp2 = ("let axioms = TRS F X \"eq(t1,t1) -> True; " ++ 
                                                     "eq(t1,t2) -> False; " ++ 
                                                     "when_else(t1,True,t2) -> t1; " ++ 
                                                     "when_else(t1,False,t2) -> t2; " ++
                                (axiomStr (old_axioms ++ axioms) "") ++"\";")    
-}
#endif

leadingSym :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym f = do
  tp<-leading_Term_Predication f
  return (extract_leading_symb tp)
 

leadingSymPos :: PosItem f => FORMULA f 
              -> (Maybe (Either OP_SYMB PRED_SYMB), [Pos])
leadingSymPos f = leading (f,False,False)
  where 
  leading (f1,b1,b2)= case (f1,b1,b2) of
                       ((Quantification _ _ f' _),_,_)  -> 
                           leading (f',b1,b2)
                       ((Negation f' _),_,_) -> 
                           leading (f',b1,b2)
                       ((Implication _ f' _ _),False,False) -> 
                           leading (f',True,False)
                       ((Equivalence f' _ _),_,False) -> 
                           leading (f',b1,True)
                       ((Definedness t _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(get_pos f1))
                       ((Predication predS _ _),_,_) -> 
                           ((Just (Right predS)),(get_pos f1))
                       ((Strong_equation t _ _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(get_pos f1))
                       ((Existl_equation t _ _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(get_pos f1))
                       _ -> (Nothing,(get_pos f1)) 

-- Sorted_term is always ignored
term :: TERM f -> TERM f
term t = case t of
           Sorted_term t' _ _ ->term t'
           _ -> t


quanti :: (FORMULA f) -> (FORMULA f)
quanti f = case f of
             Quantification _ _ f' _ -> quanti f'
             _ -> f

leading_Term_Predication :: FORMULA f -> Maybe (Either (TERM f) (FORMULA f))
leading_Term_Predication f = leading (f,False,False)
  where 
  leading (f1,b1,b2)= case (f1,b1,b2) of
                       ((Quantification _ _ f' _),_,_)  -> 
                           leading (f',b1,b2)     
                       ((Negation f' _),_,_) -> 
                           leading (f',b1,b2)
                       ((Implication _ f' _ _),False,False) -> 
                           leading (f',True,False)
                       ((Equivalence f' _ _),_,False) -> 
                           leading (f',b1,True)
                       ((Definedness t _),_,_) -> case (term t) of
                                                    Application _ _ _ -> 
                                                        return (Left (term t))
                                                    _ -> Nothing
                       ((Predication p ts ps),_,_) -> 
                           return (Right (Predication p ts ps))
                       ((Strong_equation t _ _),_,_) -> 
                           case (term t) of
                             Application _ _ _ -> return (Left (term t))
                             _ -> Nothing
                       ((Existl_equation t _ _),_,_) -> 
                           case (term t) of
                             Application _ _ _ -> return (Left (term t))
                             _ -> Nothing
                       _ -> Nothing
 


extract_leading_symb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extract_leading_symb lead = case lead of
                              Left (Application os _ _) -> Left os
                              Right (Predication p _ _) -> Right p
                              _ -> error "CASL.CCC.FreeTypes"


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


isOp_Pred :: FORMULA f -> Bool
isOp_Pred f = case f of
               Quantification _ _ f' _ -> isOp_Pred f'
               Negation f' _ -> isOp_Pred f'
               Implication _ f' _ _ -> isOp_Pred f'
               Equivalence f' _ _ -> isOp_Pred f'
               Definedness t _ -> case (term t) of
                                    (Application _ _ _) -> True
                                    _ -> False
               Predication _ _ _ -> True
               Existl_equation t _ _ -> case (term t) of 
                                          (Application _ _ _) -> True
                                          _ -> False
               Strong_equation t _ _ -> case (term t) of
                                          (Application _ _ _) -> True
                                          _-> False 
               _ -> False


partialAxiom :: FORMULA f -> Bool
partialAxiom f = case f of
                   Quantification _ _ f' _ -> partialAxiom f'
                   Negation f' _ ->
                       case f' of
                         Definedness t _ -> 
                             case (term t) of
                               Application opS _ _ -> 
                                   case (partial_OpSymb opS) of
                                     Just True -> True
                                     _ -> False
                               _ -> False
                         _ -> False
                   Implication f' _ _ _ -> 
                       case f' of
                         Definedness t _ -> 
                             case (term t) of
                               Application opS _ _ -> 
                                   case (partial_OpSymb opS) of
                                     Just True -> True
                                     _ -> False
                               _ -> False
                         _ -> False
                   Equivalence f' _ _ -> 
                       case f' of
                         Definedness t _ -> 
                             case (term t) of
                               Application opS _ _ -> 
                                   case (partial_OpSymb opS) of
                                     Just True -> True
                                     _ -> False
                               _ -> False
                         _ -> False
                   _ -> False                    


-- leadingTerm is total operation : Just True
-- leadingTerm is partial operation : Just False
-- others : Nothing
opTyp_Axiom :: FORMULA f -> Maybe Bool
opTyp_Axiom f = 
  case (leadingSym f) of
    Just (Left (Op_name _)) -> Nothing
    Just (Left (Qual_op_name _ (Op_type Total _ _ _) _)) -> Just True 
    Just (Left (Qual_op_name _ (Op_type Partial _ _ _) _)) -> Just False  
    _ -> Nothing 


type Cime = String


idStr :: Id -> String
idStr (Id ts _ _) = concat $ map tokStr ts 


{- transform Id to cime
   because cime these symbols '[' and ']' do not know, 
   these symbols are replaced by '|'       (idStrT)
-}
id_cime :: Id -> Cime 
id_cime _id = map (\s-> case s of
                            '[' -> '|'
                            ']' -> '|'
                            _ -> s) $ idStr _id


{- It filters all variables of a axiom
-}
varOfAxiom :: FORMULA f -> [VAR]
varOfAxiom f = 
  case f of
    Quantification Universal v_d _ _ -> 
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    Quantification Existential v_d _ _ -> 
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    Quantification Unique_existential v_d _ _ -> 
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    _ -> []


opSymStr :: OP_SYMB -> String 
opSymStr os = case os of
                Op_name on -> idStr on
                Qual_op_name on _ _ -> idStr on


predSymStr :: PRED_SYMB -> String
predSymStr ps = case ps of 
                  Pred_name pn -> idStr pn 
                  Qual_pred_name pn _ _ -> idStr pn


{- transform a term to cime (termStr)
-}
term_cime :: TERM f -> Cime
term_cime t = 
  case (term t) of
    Qual_var var _ _ -> tokStr var
    Application (Qual_op_name opn _ _) ts _ -> 
        if null ts then (id_cime opn)
        else ((id_cime opn) ++ "(" ++ 
             (tail $ concat $ map (\s->","++s) $ map term_cime ts)++")")
    Conditional t1 f t2 _ -> 
        ("when_else("++(term_cime t1)++","++
         (t_f_str f)++","++(term_cime t2)++")")  
              -- Achtung
    _ -> error "CASL.CCC.FreeTypes.<Termination_Term>"
  where t_f_str f=case f of                     --  condition of term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_cime t1)++","++(term_cime t2)++")")
                    _ -> error "CASL.CCC.FreeTypes.<Termination_Term-Formula>"


{- transform OP_SYMB to Signature of cime (opStr)
-}
opS_cime :: OP_SYMB -> Cime
opS_cime o_s = 
  case o_s of
    Qual_op_name op_n (Op_type _ a_sorts _ _) _ -> 
        case (length a_sorts) of 
          0 -> (id_cime op_n) ++ " : constant"
          1 -> (id_cime op_n) ++ " : unary"
          2 -> (id_cime op_n) ++ " : binary"
          _ -> (id_cime op_n) ++ " : " ++ (show $ length a_sorts) 
    _ -> error "CASL.CCC.FreeTypes.<Termination_Signature_OP_SYMB: Op_name>"


{- transform PRED_SYMB to Signature of cime (predStr)
-}
predS_cime :: PRED_SYMB -> Cime
predS_cime p_s = 
  case p_s of
    Qual_pred_name pred_n (Pred_type sts _) _ -> 
        case (length sts) of
          0 -> (id_cime pred_n) ++ " : constant"
          1 -> (id_cime pred_n) ++ " : unary"
          2 -> (id_cime pred_n) ++ " : binary"
	  _ -> (id_cime pred_n) ++ " : " ++ (show $ length sts)
    _ -> error "CASL.CCC.FreeTypes.<predS_cime>"


{- transform Implication to cime:
   i: (phi => f(t_1,...,t_m)=t)
     Example: 
                X=e => f(t_1,...,t_m)=t
     cime -->   f(t_1,...,t_m) -> U(X,t_1,...t_m);
                U(e,t_1,...t_m) -> t;
   P.S. Bool ignore

   ii: (phi1  => p(t_1,...,t_m)<=>phi)
     Example:
            X=e => p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     cime --> X=e =>  p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t  --> 
                  f(tt_1,...,tt_n) -> U1(X,p(t_1,...,t_m),tt_1,...,tt_n);
                  U1(e,True,tt_1,...,tt_n) -> t;
          --> X=e =>  f(tt_1,...,tt_n)=t => p(t_1,...,t_m)   --> 
                  p(t_1,...,t_m) -> U2(X,f(tt_1,...,tt_n),t_1,...,t_m);
                  U2(e,t,t_1,...,t_m) -> True; 
-}
impli_cime :: Int -> FORMULA f -> Cime
impli_cime index f =
  case (quanti f) of
    Implication (Strong_equation t1 t2 _) (Strong_equation t3 t4 _) _ _ ->
        case (term t1,term t3) of
          (Application _ _ _,Application _ ts _) ->
              ((term_cime t3)++" -> "++fk++"("++(term_cime t1)++
              ","++(terms_cime ts)++");"++
              fk++"("++(term_cime t2)++","++(terms_cime ts)++
              ") -> "++(term_cime t4))  
          _ -> error "CASL.CCC.FreeTypes.<impli_cime>"
    Implication f' (Equivalence (Predication predS1 ts1 _) f1 _) _ _ ->
        ""
    _ -> error "CASL.CCC.FreeTypes.<impli_cime>"
  where fk="U"++(show index)


{- transform Equivalence to cime: 
   (p(t_1,...,t_m) <=> phi)
     Example:
             p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     cime --> p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t --> 
                 f(tt_1,...,tt_n) -> U1(p(t_1,...,t_m),tt_1,...,tt_n);
                 U1(True,tt_1,...,tt_n) -> t;
          --> f(tt_1,...,tt_n)=t => p(t_1,...,t_m)  --> 
                 p(t_1,...,t_m) -> U2(f(tt_1,...,tt_n),t_1,...,t_m);
                 U2(t,t_1,...,t_m) -> True; 
-}
equiv_cime :: Int -> FORMULA f -> Cime
equiv_cime index f =
  case (quanti f) of
    Equivalence (Predication predS1 ts1 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ -> error "not implement"
	  Disjunction _ _ -> error "not implement"
          Negation _ _ -> error "not implement"
          Predication predS2 ts2 _ ->
              ((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              ")," ++ (terms_cime ts2) ++");" ++
              fk1 ++ "(True," ++ (terms_cime ts2) ++ ") -> True;" ++
              (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ 
              ")," ++ (terms_cime ts1) ++");" ++
              fk2 ++ "(True," ++ (terms_cime ts1) ++ ") -> True;")
          Strong_equation _ _ _ -> ""
	  Existl_equation _ _ _ -> ""
          _ -> error "!! " --(showPretty f1 "CASL.CCC.FreeTypes.<equiv_cime1>")
    _ -> error "CASL.CCC.FreeTypes.<equiv_cime2>"
  where fk1="U"++(show index)
        fk2="U"++(show $ index + 1)


{- transform Implication and Equivalence to cime: 
   (phi1  => p(t_1,...,t_m)<=>phi)
     Example:
            X=e => p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     cime --> X=e =>  p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t  --> 
                  f(tt_1,...,tt_n) -> U1(X,p(t_1,...,t_m),tt_1,...,tt_n);
                  U1(e,True,tt_1,...,tt_n) -> t;
          --> X=e =>  f(tt_1,...,tt_n)=t => p(t_1,...,t_m)   --> 
                  p(t_1,...,t_m) -> U2(X,f(tt_1,...,tt_n),t_1,...,t_m);
                  U2(e,t,t_1,...,t_m) -> True; 

impli_equiv_cime :: Int -> FORMULA f -> Cime
impli_equiv_cime index f = " "
-}

{- transform a axiom to cime (f_str)
-}
axiom_cime :: FORMULA f -> Cime
axiom_cime f = 
  case (quanti f) of
  --  Quantification _ _ f' _ -> axiom_cime f'
    Conjunction _ _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_Conjunction>"
    Disjunction _ _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_Disjunction>"
    Implication _ _ _ _ -> impli_cime 1 f 
 --       case f' of
 --         (Equivalence _ _ _) -> (impli_equiv_cime 1 f) 
 --         _ -> impli_cime 1 f 
    Equivalence _ _ _ -> equiv_cime 1 f
    Negation _ _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_Negation>"
    True_atom _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_True>"     
    False_atom _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_False>"
    Predication p_s ts _ -> 
        ((predSymStr p_s) ++ "(" ++ (termsStr ts) ++ ") -> True")
    Definedness _ _ -> 
        error "CASL.CCC.FreeTypes.<Termination_Axioms_Definedness>"
    Existl_equation t1 t2 _ -> 
        (term_cime t1) ++ " -> " ++ (term_cime t2)
    Strong_equation t1 t2 _ -> 
        (term_cime t1) ++ " -> " ++ (term_cime t2)                   
    _ -> error "CASL.CCC.FreeTypes.<Termination_Axioms>"
  where termsStr ts = tail $ concat $ map (\s->","++s) $ map term_cime ts


terms_cime :: [TERM f] -> Cime
terms_cime ts = tail $ concat $ map (\s->","++s) $ map term_cime ts


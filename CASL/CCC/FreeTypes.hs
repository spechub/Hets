{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

-}
{- todo
  automatic termination proof
  look at
http://cime.lri.fr/
http://elan.loria.fr/    http://www1.elsevier.com/gej-ng/31/29/23/71/22/73/entcs36006.pdf
  topic: prove termination of rewriting

  write interface to cime system, using newChildProcess (see Isabelle/IsaProves.hs)
  and pipes
  transform CASL signature to Cime signature, CASL formulas to Cime rewrite rules

Example:

spec NatJT2 = {} then
  free type Nat ::= 0 | suc(Nat)
  op __+__ : Nat*Nat->Nat
  forall x,y:Nat
  . 0+x=x
  . suc(x)+y=suc(x+y)
end

Von Hets erzeugte Theorie:

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
                                                        (var y : Nat) : Nat) : Nat) : Nat

CiME:
let F = signature "0:constant; suc:unary; +:binary";
let X = vars "x y";
let axioms = TRS F X "+(0,x) -> x; +(suc(x),y) -> suc(+(x,y)); ";
termcrit "dp";
termination axioms;
-} 

module CASL.CCC.FreeTypes where

import Debug.Trace
import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import CASL.CCC.SignFuns
import Common.AS_Annotation
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Result
import Common.Id
import Isabelle.IsaProve
import ChildProcess
import Foreign

{-
   function checkFreeType:
   - check if leading symbols are new (not in the image of morphism), if not, return Nothing
   - the leading terms consist of variables and constructors only, if not, return Nothing
     - split function leading_Symb into 
       leading_Term_Predication ::  FORMULA f -> Maybe(Either Term (Formula f))
       and 
       extract_leading_symb :: Either Term (Formula f) -> Either OP_SYMB PRED_SYMB
     - collect all operation symbols from recover_Sort_gen_ax fconstrs (= constructors)
   - no variable occurs twice in a leading term, if not, return Nothing
   - check that patterns do not overlap, if not, return Nothing This means:
       in each group of the grouped axioms:
       all patterns of leading terms/formulas are disjoint
       this means: either leading symbol is a variable, and there is just one axiom
                   otherwise, group axioms according to leading symbol
                              no symbol may be a variable
                              check recursively the arguments of constructor in each group
  - return (Just True)
-}
checkFreeType :: (PrettyPrint f, Eq f) => Morphism f e m -> [Named (FORMULA f)] 
   -> Result (Maybe Bool)
checkFreeType m fsn 
       | Set.any (\s->not $ elem s srts) newSorts =
                   let (Id _ _ ps) = head $ filter (\s->not $ elem s srts) newL
                       pos = headPos ps
                   in warning Nothing "sort s is not in srts" pos
       | Set.any (\s->not $ elem s f_Inhabited) newSorts =
                   let (Id _ _ ps) = head $ filter (\s->not $ elem s f_Inhabited) newL
                       pos = headPos ps
                   in warning (Just False) "sort s is not inhabited" pos
       | elem Nothing l_Syms =
                   let (Quantification _ _ _ ps) = head $ filter (\f->(leadingSym f) == Nothing) op_preds
                       pos = headPos ps
                   in warning Nothing "formula f is illegal" pos
       | any id $ map find_ot id_ots ++ map find_pt id_pts =    -- return Nothing
                   let pos = if any id $ map find_ot id_ots then headPos old_op_ps
                             else headPos old_pred_ps
                   in warning Nothing "leading symbol ist not new" pos
       | not $ and $ map checkTerm leadingTerms =
                   let (Application _ _ ps) = head $ filter (\t->not $ checkTerm t) leadingTerms
                       pos = headPos ps
                   in warning Nothing "the leading term consist of not only variables and constructors" pos              
       | not $ and $ map checkVar leadingTerms =
                   let (Application _ _ ps) = head $ filter (\t->not $ checkVar t) leadingTerms
                       pos = headPos ps
                   in warning Nothing "a variable occurs twice in a leading term" pos
       | not $ checkPatterns leadingPatterns =
                   let pos = headPos $ pattern_Pos leadingPatterns
                   in warning Nothing "patterns overlap" pos
       | (not $ null op_preds) && (not $ proof) = 
                   warning Nothing "not terminal" nullPos          
       | otherwise = return (Just True)
   where fs1 = map sentence (filter is_user_or_sort_gen fsn)
         fs = trace (showPretty fs1 "Axiom") fs1                   -- Axiom
         is_user_or_sort_gen ax = take 12 name == "ga_generated" || take 3 name /= "ga_"
             where name = senName ax
         sig = imageOfMorphism m
         oldSorts1 = sortSet sig
         oldSorts = trace (showPretty oldSorts1 "old sorts") oldSorts1          -- old sorts
         allSorts1 = sortSet $ mtarget m
         allSorts = trace (showPretty allSorts1 "all sorts") allSorts1
         newSorts1 = Set.filter (\s-> not $ Set.member s oldSorts) allSorts     -- new sorts
         newSorts = trace (showPretty newSorts1 "new sorts") newSorts1
         newL = Set.toList newSorts
         oldOpMap = opMap sig
         oldPredMap = predMap sig 
         fconstrs = concat $ map fc fs
         fc f = case f of
                     Sort_gen_ax constrs True -> constrs
                     _->[]
         (srts1,constructors1,_) = recover_Sort_gen_ax fconstrs
         srts = trace (showPretty srts1 "srts") srts1      --   srts
         constructors = trace (showPretty constructors1 "constructors") constructors1       -- constructors
         f_Inhabited1 = inhabited (Set.toList oldSorts) fconstrs
         f_Inhabited = trace (showPretty f_Inhabited1 "f_inhabited" ) f_Inhabited1      --  f_inhabited
         op_preds1 = filter (\f->case f of
                                  Quantification Universal _ _ _ -> True
                                  _ -> False) fs
         op_preds = trace (showPretty op_preds1 "leading") op_preds1         --  leading
         l_Syms1 = map leadingSym op_preds
         l_Syms = trace (showPretty l_Syms1 "leading_Symbol") l_Syms1         -- leading_Symbol
         op_fs = filter (\f-> case leadingSym f of
                                Just (Left _) -> True
                                _ -> False) op_preds 
         pred_fs = filter (\f-> case leadingSym f of
                                  Just (Right _) -> True
                                  _ -> False) op_preds 
         filterOp symb = case symb of
                           Just (Left (Qual_op_name ident (Total_op_type as rs _) _))->
                                [(ident, OpType {opKind=Total, opArgs=as, opRes=rs})]
                           Just (Left (Qual_op_name ident (Partial_op_type as rs _) _))->
                                [(ident, OpType {opKind=Partial, opArgs=as, opRes=rs})]
                           _ -> []
         filterPred symb = case symb of
                               Just (Right (Qual_pred_name ident (Pred_type s _) _))->
                                    [(ident, PredType {predArgs=s})]
                               _ -> [] 
         id_ots = concat $ map filterOp $ l_Syms 
         id_pts = concat $ map filterPred $ l_Syms
         old_op_ps = case head $ map leading_Term_Predication $ 
                          filter (\f->find_ot $ head $ filterOp $ leadingSym f) op_fs of
                       Just (Left (Application _ _ p)) -> p
                       _ -> []
         old_pred_ps = case head $ map leading_Term_Predication $ 
                            filter (\f->find_pt $ head $ filterPred $ leadingSym f) pred_fs of
                         Just (Right (Predication _ _ p)) -> p
                         _ -> []
         find_ot (ident,ot) = case Map.lookup ident oldOpMap of
                                  Nothing -> False
                                  Just ots -> Set.member ot ots
         find_pt (ident,pt) = case Map.lookup ident oldPredMap of
                                  Nothing -> False
                                  Just pts -> Set.member pt pts
         ltp1 = map leading_Term_Predication op_preds                 
         ltp = trace (showPretty ltp1 "leading_term_pre") ltp1              --  leading_term_pre
         leadingTerms1 = concat $ map (\tp->case tp of
                                              Just (Left t)->[t]
                                              _ -> []) $ ltp
         leadingTerms = trace (showPretty leadingTerms1 "leading Term") leadingTerms1   -- leading Term
         checkTerm (Application _ ts _) = all id $ map (\t-> case (term t) of
                                                               Qual_var _ _ _ -> True
                                                               Application op' _ _ -> elem op' constructors && 
                                                                                      checkTerm (term t) 
                                                               _ -> False) ts 
         checkVar (Application _ ts _) = overlap $ concat $ map allVarOfTerm ts
         allVarOfTerm t = case t of
                            Qual_var _ _ _ -> [t]
                            Sorted_term t' _ _ -> allVarOfTerm  t'
                            Application _ ts _ -> if length ts==0 then []
                                                  else concat $ map allVarOfTerm ts
                            _ -> [] 
         leadingPatterns1 = map (\l-> case l of                     
                                       Just (Left (Application _ ts _))->ts
                                       Just (Right (Predication _ ts _))->ts
                                       _ ->[]) $ 
                            map leading_Term_Predication op_preds
         leadingPatterns = trace (showPretty leadingPatterns1 (tmp1 ++ "\n" ++ tmp2 ++ "\n" ++ tmp ++ "\n")) leadingPatterns1    --leading Patterns
         isApp t = case t of
                     Application _ _ _->True
                     Sorted_term t' _ _ ->isApp t'
                     _ -> False
         isVar t = case t of
                     Qual_var _ _ _ ->True
                     Sorted_term t' _ _ ->isVar t'
                     _ -> False
         allIdentic ts = all (\t-> t== (head ts)) ts
         overlap ts = let check [] = True
                          check (p:ps)=if elem p ps then False
                                       else check ps
                      in check ts 
         patternsOfTerm t = case t of
                              Application (Qual_op_name _ _ _) ts _-> ts
                              Sorted_term t' _ _ -> patternsOfTerm t'
                              _ -> []
         sameOps app1 app2 = case (term app1) of
                               Application ops1 _ _ -> case (term app2) of
                                                         Application ops2 _ _ -> ops1==ops2
                                                         _ -> False
                               _ -> False
         group [] = []
         group ps = (filter (\p1-> sameOps (head p1) (head (head ps))) ps):
                      (group $ filter (\p2-> not $ sameOps (head p2) (head (head ps))) ps)
         checkPatterns ps 
                | length ps <=1 = True
                | allIdentic ps = False
                | all isVar $ map head ps = if allIdentic $ map head ps then checkPatterns $ map tail ps
                                            else False
                | all (\p-> sameOps p (head (head ps))) $ map head ps = 
                                            checkPatterns $ map (\p'->(patternsOfTerm $ head p')++(tail p')) ps 
                | all isApp $ map head ps = all id $ map checkPatterns $ group ps
                | otherwise = False
         term_Pos t = case term t of
                        Application _ _ p -> p                                                                                    
                        Qual_var _ _ p -> p                                                                                       
                        _ -> []      
         pattern_Pos pas
                | length pas <=1 = []
                | allIdentic pas = term_Pos $ head $ head pas
                | not $ all isApp $ map head pas = term_Pos $ head $ filter (\t-> isVar t) $ map head pas
                | all isVar $ map head pas = if allIdentic $ map head pas then pattern_Pos $ map tail pas
                                            else term_Pos $ head $ map head pas 
                | all (\p-> sameOps p (head (head pas))) $ map head pas =
                                            pattern_Pos $ map (\p'->(patternsOfTerm $ head p')++(tail p')) pas
        --        | all isApp $ map head pas = concat $ map pattern_Pos $ group ps
                | otherwise = concat $ map pattern_Pos $ group pas
                  
{-
         checkMatrix ps 
                | length ps <=1 = True
                | allIdentic ps = False
                | all isVar $ map head ps = if allIdentic $ map head ps then checkMatrix $ map tail ps
                                            else False
                | all (\p-> sameOps p (head (head ps))) $ map head ps = 
                                            checkMatrix $ map (\p'->(patternsOfTerm $ head p')++(tail p')) ps 
                | all isApp $ map head ps = all id $ map checkMatrix $ group ps
                | otherwise = False
     
         checkPatterns [] = True
         checkPatterns ps
                | (length ps) == 1 = overlap $ filter (\t->case (term t) of
                                                             Qual_var _ _ _ ->True
                                                             _ -> False) $ head ps
                | otherwise = checkMatrix ps
-}
         term t = case t of
                    Sorted_term t' _ _ ->term t'
                    _ -> t
         -- Termination
         idStr (Id ts _ _) = if (tokStr (head ts)) == "__" then (tokStr (head (tail ts)))
                             else tokStr (head ts) 
         rP cp = do
            msg <- readMsg cp
            case msg of
              "Termination proof found." -> return True
              "Quitting." -> return False
              _ -> rP cp
         opStr o_s = case o_s of
                       Qual_op_name op_n (Total_op_type a_sorts _ _) _ -> case (length a_sorts) of 
                                                                            0 -> (idStr op_n) ++ " : constant"
                                                                            1 -> (idStr op_n) ++ " : unary"
                                                                            2 -> (idStr op_n) ++ " : binary"
                                                                            _ -> error "Termination_Signature"
                       Qual_op_name op_n (Partial_op_type a_sorts _ _) _ -> case (length a_sorts) of 
                                                                            0 -> (idStr op_n) ++ " : constant"
                                                                            1 -> (idStr op_n) ++ " : unary"
                                                                            2 -> (idStr op_n) ++ " : binary"
                                                                            _ -> error "Termination_Signature"
                       _ -> error "Termination_Signature"
         sigComb sig1 sig2 | null sig2 =sig1
                           | otherwise = case (head sig2) of
                                           Just (Left o_s) -> if elem o_s sig1 then sigComb sig1 (tail sig2)
                                                              else sigComb (o_s:sig1) (tail sig2)
                                           Just (Right _) -> sigComb sig1 (tail sig2) 
                                           _ -> error "Termination_Signature" 
         signStr signs str
                 | null signs = str
                 | otherwise = signStr (tail signs) (str ++ (opStr $ head signs) ++ "; ")
           --      | otherwise = if null str then signStr (tail signs) (str ++ (opStr $ head signs))
           --                    else signStr (tail signs) (str ++ "; " ++ (opStr $ head signs))
         varOfAxiom f = case f of
                          Quantification Universal v_d _ _ -> concat $  map (\v-> case v of
                                                                                   Var_decl vs _ _ -> vs
                                                                                   _ -> error "Termination_Variable") v_d 
                          _ -> error "Termination_Variable"
         varsStr vars str
                 | null vars = str
                 | otherwise = if null str then varsStr (tail vars) (str ++ (tokStr $ head vars))
                               else varsStr (tail vars) (str ++ " " ++ (tokStr $ head vars))
         f_str f = case f of
                     Quantification Universal _ f' _ -> f_str f' 
                     Implication _ f' _ _ -> f_str f' 
                     Strong_equation t1 t2 _ -> (termStr t1) ++ " -> " ++ (termStr t2)                   
                     Existl_equation t1 t2 _ -> (termStr t1) ++ " -> " ++ (termStr t2)
                     _ -> error "Termination_Axioms"
         termStr t = case (term t) of
                       (Qual_var var _ _) -> tokStr var
                       (Application (Qual_op_name opn _ _) ts _) -> if null ts then (idStr opn)
                                                                    else ((idStr opn) ++ "(" ++ 
                                                                         (tail $ concat $ map (\s->"," ++ s) $ map termStr ts) ++ ")")
                       _ -> error "Termination_Term"
         axiomStr axioms str 
                 | null axioms = str
                 | otherwise = axiomStr (tail axioms) (str ++ (f_str $ (head axioms)) ++ "; ")                    
         proof = unsafePerformIO (do
                 cim <- newChildProcess "/home/xinga/bin/cime" []
   --              sendMsg cim "let F = signature \"0 : constant;suc : unary;+ : binary\";"
                 sendMsg cim ("let F = signature \"" ++ (signStr (sigComb constructors l_Syms) "") ++ "\";")     
   --              sendMsg cim "let X = vars \"x y\";"
                 sendMsg cim ("let X = vars \"" ++ (varsStr (varOfAxiom $ (head op_preds)) "") ++ "\";")        
   --              sendMsg cim "let axioms = TRS F X \"+(0,x) -> x; +(suc(x),y) -> suc(+(x,y));\";"
                 sendMsg cim ("let axioms = TRS F X \"" ++ (axiomStr op_preds "") ++"\";")    --3
                 sendMsg cim "termcrit \"dp\";"
                 sendMsg cim "termination axioms;"
                 sendMsg cim "#quit;"
                 res <-rP cim
                 return res)
         tmp = ("let axioms = TRS F X \"" ++ (axiomStr op_preds "") ++"\";")
         tmp1 = ("let F = signature \"" ++ (signStr (sigComb constructors l_Syms) "") ++ "\";")
         tmp2 = ("let X = vars \"" ++ (varsStr (varOfAxiom $ (head op_preds)) "") ++ "\";")                              
    
leadingSym :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym f = do
       tp<-leading_Term_Predication f
       return (extract_leading_symb tp)
 
{-
leadingSymb :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSymb f = leading (f,False,False)
  where leading (f,b1,b2)= case (f,b1,b2) of
                            ((Quantification Universal _ f' _),b1',b2')  -> leading (f',b1',b2')
                            ((Implication _ f' _ _),False,False) -> leading (f',True,False)
                            ((Equivalence f' _ _),b,False) -> leading (f',b,True)
                            ((Predication predS _ _),_,_) -> return (Right predS)
                            ((Strong_equation t _ _),_,_) -> case (term t) of
                                                              Application opS _ _ -> return (Left opS)                 
                                                              _ -> Nothing
                            ((Existl_equation t _ _),_,_) -> case (term t) of
                                                              Application opS _ _ -> return (Left opS)
                                                              _ -> Nothing
                            _ -> Nothing 
        term t = case t of
                  Sorted_term t' _ _ ->term t'
                  _ -> t
-}
 

leading_Term_Predication ::  FORMULA f -> Maybe (Either (TERM f) (FORMULA f))
leading_Term_Predication f = leading (f,False,False)
  where leading (f,b1,b2)= case (f,b1,b2) of
                            ((Quantification Universal _ f' _),_,_)  -> leading (f',b1,b2)
                            ((Implication _ f' _ _),False,False) -> leading (f',True,False)
                            ((Equivalence f' _ _),b,False) -> leading (f',b,True)
                            ((Predication p ts ps),_,_) -> return (Right (Predication p ts ps))
                            ((Strong_equation t _ _),_,_) -> case (term t) of
                                                              Application _ _ _ -> return (Left (term t))
                                                              _ -> Nothing
                            ((Existl_equation t _ _),_,_) -> case (term t) of
                                                              Application _ _ _ -> return (Left (term t))
                                                              _ -> Nothing
                            _ -> Nothing

        term t = case t of
                  Sorted_term t' _ _ ->term t'
                  _ -> t
 


extract_leading_symb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extract_leading_symb lead = case lead of
                              Left (Application os _ _) -> Left os
                              Right (Predication p _ _) -> Right p

{- group the axioms according to their leading symbol
   output Nothing if there is some axiom in incorrect form -}
groupAxioms :: [FORMULA f] -> Maybe [(Either OP_SYMB PRED_SYMB,[FORMULA f])]
groupAxioms phis = do
  symbs <- mapM leadingSym phis
  return (filterA (zip symbs phis) [])
    where filterA [] _=[]
          filterA (p:ps) symb=let fp=fst p
                                  p'= if elem fp symb then []
                                      else [(fp,snd $ unzip $ filter (\p'->(fst p')==fp) (p:ps))]
                                  symb'= if not $ (elem fp symb) then fp:symb
                                         else symb
                              in p'++(filterA ps symb')
{-
instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
  printText0 ga (Left x) = printText0 ga x
  printText0 ga (Right x) = printText0 ga x

instance PrettyPrint a => PrettyPrint (Maybe a) where
  printText0 ga (Just x) = printText0 ga x
  printText0 ga Nothing = ptext "Nothing"
-}
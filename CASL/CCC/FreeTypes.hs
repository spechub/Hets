{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

-}
{- todo
   extend function checkFreeType:
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

module CASL.CCC.FreeTypes where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import CASL.CCC.SignFuns

checkFreeType :: Eq f=> Morphism f e m -> [FORMULA f] -> Maybe Bool
checkFreeType m fs 
       | any (\s->not $ elem s srts) sorts = Nothing
       | all (\s->not $ elem s f_Inhabited) sorts = Just False
       | elem Nothing l_Syms =  Nothing
       | (any id $ map (\s->elem s sorts) $ ops_sorts++preds_sorts) =Nothing
       | not $ and $ map checkTerm leadingTerms =Nothing
       | not $ and $ map checkVar leadingTerms =Nothing 
       | not $ and $ map checkPatterns leadingPatterns=Nothing
       | otherwise = Just True
   where sig = imageOfMorphism m
         sorts= Set.toList (sortSet sig)
         fconstrs= concat $ map fc fs
         fc f= case f of
                     Sort_gen_ax constrs True -> constrs
                     _->[]
         (srts,constructors,_)=recover_Sort_gen_ax fconstrs 
         f_Inhabited=inhabited fconstrs
         op_preds= filter (\f->case f of
                                 Quantification _ _ _ _ -> True
                                 _ -> False) fs
         l_Syms=map leadingSym op_preds
         filterOp symb= case symb of
                         Just (Left (Qual_op_name _ op _))->[res_OP_TYPE op]
                         _ ->[]
         filterPred symb=case symb of
                               Just (Right (Qual_pred_name _ (Pred_type s _) _))->s
                               _ -> [] 
         ops_sorts=concat $ map filterOp $ l_Syms 
         preds_sorts=concat $ map filterPred $ l_Syms
         leadingTerms=concat $ map (\tp->case tp of
                                             Just (Left t)->[t]
                                             _ -> []) $ 
                      map leading_Term_Predication fs
         checkTerm (Application op ts _) =elem op constructors &&
                                          all (\t-> case t of
                                                     Qual_var _ _ _-> True
                                                     _ -> False) ts
         checkVar (Application _ ts _)=let check [] = True
                                           check (p:ps)=if elem p ps then False
                                                        else check ps
                                       in check ts
         leadingPatterns=map (\l-> case l of
                                     Just (Left (Application _ ts _))->ts
                                     Just (Right (Predication _ ts _))->ts) $ 
                         map leading_Term_Predication fs
         isNil t = case t of
                     Application _ ts _-> if length ts==0 then True
                                          else False
                     _ -> False
         isCons t = case t of
                      Application _ ts _-> if length ts>0 then True
                                          else False
                      _ -> False
         isApp t = case t of
                     Application _ _ _->True
                     _ -> False
         isVar t = case t of
                     Qual_var _ _ _ ->True
                     _ -> False
         allIdentic ts= all (\t-> t== (head ts)) ts           
         patternsOfTerm t= case t of
                              Application (Qual_op_name _ _ _) ts _->ts
                              _ -> []
         checkMatrix ps 
                | length ps <=1 = True
                | allIdentic ps = False
                | all isApp $ map head ps = (checkMatrix $ map tail $ filter (\p->isNil $ head p) ps) &&
                                            (checkMatrix $ map (\p'->(patternsOfTerm $ head p')++(tail p')) $ 
                                                                             filter (\p->isCons $ head p) ps)
                | all isVar $ map head ps = if allIdentic $ map head ps then checkMatrix $ map tail ps
                                            else False
                | otherwise = False     
         checkPatterns [] = True
         checkPatterns ts
                | length ts==1 =(all isVar $ patternsOfTerm $ head ts)&& (checkVar $ head ts)
                | otherwise = checkMatrix $ map patternsOfTerm ts
    
leadingSym :: FORMULA f -> Maybe(Either OP_SYMB PRED_SYMB)
leadingSym f = do
       tp<-leading_Term_Predication f
       return (extract_leading_symb tp) 
{-
leadingSym :: FORMULA f -> Maybe(Either OP_SYMB PRED_SYMB)
leadingSym f = leading (f,False,False)
  where leading (f,b1,b2)= case (f,b1,b2) of
                            ((Quantification Universal _ f' _),_,_)  -> leading (f',b1,b2)
                            ((Implication _ f' _ _),False,False) -> leading (f',True,False)
                            ((Equivalence f' _ _),b,False) -> leading (f',b,True)
                            ((Predication predS _ _),_,_) -> return (Right predS)
                            ((Strong_equation t _ _),_,_) -> case t of
                                                              Application opS _ _ -> return (Left opS)                 
                                                              _ -> Nothing
                            ((Existl_equation t _ _),_,_) -> case t of
                                                              Application opS _ _ -> return (Left opS)
                                                              _ -> Nothing
                            _ -> Nothing 
-}          

leading_Term_Predication ::  FORMULA f -> Maybe(Either (TERM f) (FORMULA f))
leading_Term_Predication f =leading (f,False,False)
  where leading (f,b1,b2)= case (f,b1,b2) of
                            ((Quantification Universal _ f' _),_,_)  -> leading (f',b1,b2)
                            ((Implication _ f' _ _),False,False) -> leading (f',True,False)
                            ((Equivalence f' _ _),b,False) -> leading (f',b,True)
                            ((Predication p ts ps),_,_) -> return (Right (Predication p ts ps))
                            ((Strong_equation t _ _),_,_) -> case t of
                                                              Application _ _ _ -> return (Left t)
                                                              _ -> Nothing
                            ((Existl_equation t _ _),_,_) -> case t of
                                                              Application _ _ _ -> return (Left t)
                                                              _ -> Nothing
                            _ -> Nothing

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
                                      else [(fp,snd$unzip$filter (\p'->(fst p')==fp) (p:ps))]
                                  symb'= if not $ (elem fp symb) then fp:symb
                                         else symb
                              in p'++(filterA ps symb')
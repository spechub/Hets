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

checkFreeType :: Morphism f e m -> [FORMULA f] -> Maybe Bool
checkFreeType m fs=if any (\s->not $ elem s srts) sorts then Nothing
                   else if all (\s->not $ elem s f_Inhabited) sorts then Just False
                        else if elem Nothing $ map leadingSym op_preds then Nothing
                             else Just True
   where sig = imageOfMorphism m
         sorts= Set.toList (sortSet sig)
         fconstrs= concat $ map fc fs
         fc f= case f of
                     Sort_gen_ax constrs True -> constrs
                     _->[]
         (srts,_,_)=recover_Sort_gen_ax fconstrs 
         f_Inhabited=inhabited fconstrs
         op_preds= filter (\f->case f of
                                 Quantification _ _ _ _ -> True
                                 _ -> False) fs


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
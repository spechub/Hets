{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

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
                        else if elem Nothing $ map leadingSym fs then Nothing
                             else Just True
   where sig = imageOfMorphism m
         sorts= Set.toList (sortSet sig)
         fconstrs= concat $ map fc fs
         fc f= case f of
                     Sort_gen_ax constrs True -> constrs
                     _->[]
         (srts,_,_)=recover_Sort_gen_ax fconstrs 
         f_Inhabited=inhabited fconstrs
         leadingSym f=case f of
                       Quantification Universal _ f' _  -> leadingSym f'
                       Implication _ f' _ _ -> leadingSym f'
                       Equivalence f' _ _ -> leadingSym f'
                       Predication predS _ _ -> return (Right predS)
                       Strong_equation t1 t2 _ -> case t1 of
                                                   Application opS _ _ -> case t2 of
                                                                           Sorted_term _ s _ ->
                                                                             if elem s sorts then return (Left opS)
                                                                             else Nothing
                                                                           _ -> Nothing
                                                   _ -> Nothing
                       _ -> Nothing                                           
{-         
leadingSym :: FORMULA f -> Maybe(Either OP_SYMB PRED_SYMB)
leadingSym f= case f of
                Quantification Universal _ f' _  -> leadingSym f'
                Implication _ f' _ _ -> leadingSym f'
                Equivalence f' _ _ -> leadingSym f' 
                Predication predS _ _ -> return (Right predS)
                Strong_equation t1 t2 _ -> case t1 of
                                             Application opS _ _ -> case t2 of
                                                                      Sorted_term _ s _ ->
                                                                        if elem s sorts then return (Left opS)
                                                                        else Nothing
                                                                      _ -> Nothing                  
                                             _ -> Nothing
                _ -> Nothing
-}
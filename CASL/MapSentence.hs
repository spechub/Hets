
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
rename symbols of sentences according to a signature morphisms

-}

module CASL.MapSentence where

import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import Common.Id
import Common.Result

mapSrt :: Morphism f e m -> SORT -> SORT
mapSrt m = mapSort (sort_map m)

mapTerm :: 
           Morphism f e m -> TERM f -> Result (TERM f)
mapTerm m t = case t of
   Qual_var v s ps -> return $ Qual_var v (mapSrt m s) ps
   Application o ts ps -> do 
       newTs <- mapM (mapTerm m) ts
       newO <- mapOpSymb m o 
       return $ Application newO newTs ps
   Sorted_term st s ps -> do
       newT <- mapTerm m st
       return $ Sorted_term newT (mapSrt m s) ps
   Cast st s ps -> do
       newT <- mapTerm m st
       return $ Cast newT (mapSrt m s) ps
   Conditional t1 f t2 ps -> do
       t3 <- mapTerm m t1
       newF <- mapSen m f
       t4 <- mapTerm m t2
       return $ Conditional t3 newF t4 ps 
   _ -> error "mapTerm"

mapOpSymb :: 
             Morphism f e m -> OP_SYMB -> Result OP_SYMB
mapOpSymb m os@(Qual_op_name i t ps) = do 
   (j, ty) <- maybeToResult (posOfId i) 
	      ("no mapping for: " ++ showPretty os "") $ 
	      mapOpSym (sort_map m) (fun_map m) (i, toOpType t)
   return $ Qual_op_name j (toOP_TYPE ty) ps
mapOpSymb _ os = error ("mapOpSymb: unexpected op symb: "++ showPretty os "")

mapVars :: Morphism f e m -> VAR_DECL -> VAR_DECL
mapVars m (Var_decl vs s ps) = Var_decl vs (mapSrt m s) ps

mapSen :: 
          Morphism f e m -> FORMULA f -> Result (FORMULA f)
mapSen m f = case f of 
   Quantification q vs qf ps -> do
       newF <- mapSen m qf
       return $ Quantification q (map (mapVars m) vs) newF ps
   Conjunction fs ps -> do
       newFs <- mapM (mapSen m) fs
       return $ Conjunction newFs ps
   Disjunction fs ps -> do
       newFs <- mapM (mapSen m) fs
       return $ Disjunction newFs ps
   Implication f1 f2 b ps -> do
       f3 <- mapSen m f1
       f4 <- mapSen m f2
       return $ Implication f3 f4 b ps
   Equivalence f1 f2 ps -> do
       f3 <- mapSen m f1
       f4 <- mapSen m f2
       return $ Equivalence f3 f4 ps
   Negation nf ps -> do
       newF <- mapSen m nf
       return $ Negation newF ps
   True_atom _ -> return f
   False_atom _ -> return f
   Predication p ts ps -> do 
       newTs <- mapM (mapTerm m) ts
       newP <- mapPrSymb m p
       return $ Predication newP newTs ps
   Definedness t ps -> do 
       newT <- mapTerm m t
       return $ Definedness newT ps
   Existl_equation t1 t2 ps -> do
       t3 <- mapTerm m t1
       t4 <- mapTerm m t2
       return $ Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> do
       t3 <- mapTerm m t1
       t4 <- mapTerm m t2
       return $ Strong_equation t3 t4 ps
   Membership t s ps -> do 
       newT <- mapTerm m t
       return $ Membership newT (mapSrt m s) ps
   _ -> error "mapSen"

mapPrSymb :: 
             Morphism f e m -> PRED_SYMB -> Result PRED_SYMB
mapPrSymb m p@(Qual_pred_name i t ps) = do 
   (j, ty) <- maybeToResult (posOfId i) 
	      ("no mapping for: " ++ showPretty p "") $ 
	      mapPredSym (sort_map m) (pred_map m) (i, toPredType t)
   return $ Qual_pred_name j (toPRED_TYPE ty) ps
mapPrSymb _ p = error ("mapPrSymb: unexpected pred symb: "++ showPretty p "")

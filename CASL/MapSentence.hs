
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

mapTerm :: MapSen f e m -> Morphism f e m -> TERM f -> Result (TERM f)
mapTerm mf m t = case t of
   Qual_var v s ps -> return $ Qual_var v (mapSrt m s) ps
   Application o ts ps -> do 
       newTs <- mapM (mapTerm mf m) ts
       newO <- mapOpSymb m o 
       return $ Application newO newTs ps
   Sorted_term st s ps -> do
       newT <- mapTerm mf m st
       return $ Sorted_term newT (mapSrt m s) ps
   Cast st s ps -> do
       newT <- mapTerm mf m st
       return $ Cast newT (mapSrt m s) ps
   Conditional t1 f t2 ps -> do
       t3 <- mapTerm mf m t1
       newF <- mapSen mf m f
       t4 <- mapTerm mf m t2
       return $ Conditional t3 newF t4 ps 
   _ -> error "mapTerm"

mapOpSymb :: Morphism f e m -> OP_SYMB -> Result OP_SYMB
mapOpSymb m os@(Qual_op_name i t ps) = do 
   (j, ty) <- maybeToResult (posOfId i) 
	      ("no mapping for: " ++ showPretty os "") $ 
	      mapOpSym (sort_map m) (fun_map m) (i, toOpType t)
   return $ Qual_op_name j (toOP_TYPE ty) ps
mapOpSymb _ os = error ("mapOpSymb: unexpected op symb: "++ showPretty os "")

mapVars :: Morphism f e m -> VAR_DECL -> VAR_DECL
mapVars m (Var_decl vs s ps) = Var_decl vs (mapSrt m s) ps

mapDecoratedOpSymb :: Morphism f e m -> 
                        (OP_SYMB,[Int]) -> Result (OP_SYMB,[Int])
mapDecoratedOpSymb m (os,indices) = do
   newOs <- mapOpSymb m os
   return (newOs,indices)

mapConstr :: Morphism f e m -> Constraint -> Result Constraint
mapConstr m constr = do
   let newS = mapSrt m (newSort constr)
   newOps <- mapM (mapDecoratedOpSymb m) (opSymbs constr)
   return (constr {newSort = newS, opSymbs = newOps})

type MapSen f e m = Morphism f e m -> f -> Result f 

mapSen :: MapSen f e m -> Morphism f e m -> FORMULA f -> Result (FORMULA f)
mapSen mf m f = case f of 
   Quantification q vs qf ps -> do
       newF <- mapSen mf m qf
       return $ Quantification q (map (mapVars m) vs) newF ps
   Conjunction fs ps -> do
       newFs <- mapM (mapSen mf m) fs
       return $ Conjunction newFs ps
   Disjunction fs ps -> do
       newFs <- mapM (mapSen mf m) fs
       return $ Disjunction newFs ps
   Implication f1 f2 b ps -> do
       f3 <- mapSen mf m f1
       f4 <- mapSen mf m f2
       return $ Implication f3 f4 b ps
   Equivalence f1 f2 ps -> do
       f3 <- mapSen mf m f1
       f4 <- mapSen mf m f2
       return $ Equivalence f3 f4 ps
   Negation nf ps -> do
       newF <- mapSen mf m nf
       return $ Negation newF ps
   True_atom _ -> return f
   False_atom _ -> return f
   Predication p ts ps -> do 
       newTs <- mapM (mapTerm mf m) ts
       newP <- mapPrSymb m p
       return $ Predication newP newTs ps
   Definedness t ps -> do 
       newT <- mapTerm mf m t
       return $ Definedness newT ps
   Existl_equation t1 t2 ps -> do
       t3 <- mapTerm mf m t1
       t4 <- mapTerm mf m t2
       return $ Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> do
       t3 <- mapTerm mf m t1
       t4 <- mapTerm mf m t2
       return $ Strong_equation t3 t4 ps
   Membership t s ps -> do 
       newT <- mapTerm mf m t
       return $ Membership newT (mapSrt m s) ps
   Sort_gen_ax constrs isFree -> do
       newConstrs <- mapM (mapConstr m) constrs
       return $ Sort_gen_ax newConstrs isFree
   ExtFORMULA ef -> do 
       newF <- mf m ef 
       return $ ExtFORMULA newF	       
   _ -> error "mapSen"

mapPrSymb :: 
             Morphism f e m -> PRED_SYMB -> Result PRED_SYMB
mapPrSymb m p@(Qual_pred_name i t ps) = do 
   (j, ty) <- maybeToResult (posOfId i) 
	      ("no mapping for: " ++ showPretty p "") $ 
	      mapPredSym (sort_map m) (pred_map m) (i, toPredType t)
   return $ Qual_pred_name j (toPRED_TYPE ty) ps
mapPrSymb _ p = error ("mapPrSymb: unexpected pred symb: "++ showPretty p "")

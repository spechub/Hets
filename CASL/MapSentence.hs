
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
import Common.Result

mapSrt :: Morphism f e m -> SORT -> SORT
mapSrt m = mapSort (sort_map m)

type MapSen f e m = Morphism f e m -> f -> f 

mapTerm :: MapSen f e m -> Morphism f e m -> TERM f -> TERM f
mapTerm mf m t = case t of
   Qual_var v s ps -> Qual_var v (mapSrt m s) ps
   Application o ts ps -> let 
       newTs = map (mapTerm mf m) ts
       newO = mapOpSymb m o 
       in Application newO newTs ps
   Sorted_term st s ps -> let
       newT = mapTerm mf m st
       in Sorted_term newT (mapSrt m s) ps
   Cast st s ps -> let
       newT = mapTerm mf m st
       in Cast newT (mapSrt m s) ps
   Conditional t1 f t2 ps -> let
       t3 = mapTerm mf m t1
       newF = mapSen mf m f
       t4 = mapTerm mf m t2
       in Conditional t3 newF t4 ps 
   _ -> error "mapTerm"

mapOpSymb :: Morphism f e m -> OP_SYMB -> OP_SYMB
mapOpSymb m (Qual_op_name i t ps) =  
   let (j, ty) = mapOpSym (sort_map m) (fun_map m) (i, toOpType t)
   in Qual_op_name j (toOP_TYPE ty) ps
mapOpSymb _ os = error ("mapOpSymb: unexpected op symb: "++ showPretty os "")

mapVars :: Morphism f e m -> VAR_DECL -> VAR_DECL
mapVars m (Var_decl vs s ps) = Var_decl vs (mapSrt m s) ps

mapDecoratedOpSymb :: Morphism f e m -> (OP_SYMB,[Int]) -> (OP_SYMB,[Int])
mapDecoratedOpSymb m (os,indices) = let
   newOs = mapOpSymb m os
   in (newOs,indices)

mapConstr :: Morphism f e m -> Constraint -> Constraint
mapConstr m constr = 
   let newS = mapSrt m (newSort constr)
       newOps = map (mapDecoratedOpSymb m) (opSymbs constr)
   in (constr {newSort = newS, opSymbs = newOps})

mapSen :: MapSen f e m -> Morphism f e m -> FORMULA f -> FORMULA f
mapSen mf m f = case f of 
   Quantification q vs qf ps -> let
       newF = mapSen mf m qf
       in Quantification q (map (mapVars m) vs) newF ps
   Conjunction fs ps -> let
       newFs = map (mapSen mf m) fs
       in Conjunction newFs ps
   Disjunction fs ps -> let
       newFs = map (mapSen mf m) fs
       in Disjunction newFs ps
   Implication f1 f2 b ps -> let
       f3 = mapSen mf m f1
       f4 = mapSen mf m f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = mapSen mf m f1
       f4 = mapSen mf m f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = mapSen mf m nf
       in Negation newF ps
   True_atom _ -> f
   False_atom _ -> f
   Predication p ts ps -> let 
       newTs = map (mapTerm mf m) ts
       newP = mapPrSymb m p
       in Predication newP newTs ps
   Definedness t ps -> let 
       newT = mapTerm mf m t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = mapTerm mf m t1
       t4 = mapTerm mf m t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = mapTerm mf m t1
       t4 = mapTerm mf m t2
       in Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = mapTerm mf m t
       in Membership newT (mapSrt m s) ps
   Sort_gen_ax constrs isFree -> let
       newConstrs = map (mapConstr m) constrs
       in Sort_gen_ax newConstrs isFree
   ExtFORMULA ef -> let 
       newF = mf m ef 
       in ExtFORMULA newF	       
   _ -> error "mapSen"

mapPrSymb :: Morphism f e m -> PRED_SYMB -> PRED_SYMB
mapPrSymb m (Qual_pred_name i t ps) =  
   let (j, ty) = mapPredSym (sort_map m) (pred_map m) (i, toPredType t)
   in Qual_pred_name j (toPRED_TYPE ty) ps
mapPrSymb _ p = error ("mapPrSymb: unexpected pred symb: "++ showPretty p "")

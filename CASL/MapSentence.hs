{- |
Module      :  $Header$
Description :  rename symbols of sentences according to a signature morphisms
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Rename symbols of sentences according to a signature morphisms
-}

module CASL.MapSentence where

import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Fold

mapSrt :: Morphism f e m -> SORT -> SORT
mapSrt = mapSort . sort_map

type MapSen f e m = Morphism f e m -> f -> f

mapMorphism :: MapSen f e m -> Morphism f e m
          -> Record f (FORMULA f) (TERM f)
mapMorphism mf m = (mapRecord $ mf m)
     { foldQual_var = \ _ v -> Qual_var v . mapSrt m
     , foldApplication = \ _ -> Application . mapOpSymb m
     , foldSorted_term = \ _ st -> Sorted_term st . mapSrt m
     , foldCast = \ _ st -> Cast st . mapSrt m
     , foldQuantification = \ _ q ->
           Quantification q . map (mapVars m)
     , foldPredication = \ _ -> Predication . mapPrSymb m
     , foldMembership = \ _ t -> Membership t . mapSrt m
     , foldSort_gen_ax = \ _ constrs isFree -> let
       newConstrs = map (mapConstr m) constrs in Sort_gen_ax newConstrs isFree
     }

mapTerm :: MapSen f e m -> Morphism f e m -> TERM f -> TERM f
mapTerm mf = foldTerm . mapMorphism mf

mapSen :: MapSen f e m -> Morphism f e m -> FORMULA f -> FORMULA f
mapSen mf m = if isInclusionMorphism (const True) m then id else
  foldFormula $ mapMorphism mf m

mapOpSymb :: Morphism f e m -> OP_SYMB -> OP_SYMB
mapOpSymb m (Qual_op_name i t ps) =
   let (j, ty) = mapOpSym (sort_map m) (op_map m) (i, toOpType t)
   in Qual_op_name j (toOP_TYPE ty) ps
mapOpSymb _ (Op_name os) =
    error $ "mapOpSymb: unexpected op symb: " ++ show os

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

mapPrSymb :: Morphism f e m -> PRED_SYMB -> PRED_SYMB
mapPrSymb m (Qual_pred_name i t ps) =
   let (j, ty) = mapPredSym (sort_map m) (pred_map m) (i, toPredType t)
   in Qual_pred_name j (toPRED_TYPE ty) ps
mapPrSymb _ (Pred_name p) =
    error $ "mapPrSymb: unexpected pred symb: " ++ show p

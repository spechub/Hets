{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable


-}

module CASL.CCC.SignFuns where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

-- | Compute the image of a signature morphism

imageOfMorphism :: Morphism f e m  -> Sign f e
imageOfMorphism m =
        sig {sortSet = Map.image sortMap (sortSet src),
             sortRel = Rel.image (\a->Map.find a sortMap) (sortRel src),
             opMap = Map.foldWithKey
                       (\ident ots l ->
                           Set.fold (\ot l' -> insertOp
                             (mapOpSym sortMap funMap (ident,ot)) l') l ots)
                       Map.empty (opMap src),
             predMap = Map.foldWithKey
                         (\ident pts l ->
                             Set.fold (\pt l' -> insertPred
                               (mapPredSym sortMap pMap (ident,pt)) l') l pts)
                         Map.empty (predMap src)
            }
    where sig = mtarget m
          src = msource m
          sortMap = sort_map m
          funMap = fun_map m
          insertOp (ident,ot) opM =
            case Map.lookup ident opM of
              Nothing -> Map.insert ident (Set.single ot) opM
              Just ots -> Map.insert ident (Set.insert ot ots) opM
          pMap = pred_map m
          insertPred (ident,pt) predM =
            case Map.lookup ident predM of
              Nothing -> Map.insert ident (Set.single pt) predM
              Just pts -> Map.insert ident (Set.insert pt pts) predM

{-
imageOfMorphism :: Morphism f e m  -> Sign f e
imageOfMorphism m = 
        sig {sortSet = Map.image sortMap (sortSet src),
             sortRel = Rel.image (\a->Map.find a sortMap) (sortRel src), 
             opMap = Map.foldWithKey 
                       (\ident ots l ->  
                           Set.fold (\ot l' -> 
                             case mapOpSym sortMap funMap (ident,ot) of
                               Nothing -> l'
                               Just id_ot -> insertOp id_ot l') l ots) 
                       Map.empty (opMap src),
             predMap = Map.foldWithKey                                          
                         (\ident pts l ->                                         
                             Set.fold (\pt l' ->                                  
                               case mapPredSym sortMap pMap (ident,pt) of      
                                 Nothing -> l'                                    
                                 Just id_pt -> insertPred id_pt l') l pts)        
                         Map.empty (predMap src)              
            }
    where sig = mtarget m
          src = msource m
          sortMap = sort_map m
          funMap = fun_map m
          insertOp (ident,ot) opM = 
            case Map.lookup ident opM of
              Nothing -> Map.insert ident (Set.single ot) opM
              Just ots -> Map.insert ident (Set.insert ot ots) opM
          pMap = pred_map m
          insertPred (ident,pt) predM = 
            case Map.lookup ident predM of
              Nothing -> Map.insert ident (Set.single pt) predM
              Just pts -> Map.insert ident (Set.insert pt pts) predM

-}
inhabited :: [Constraint] -> [SORT]
inhabited constrs = iterateInhabited []
      where (_,ops,_)=recover_Sort_gen_ax constrs
            argsAndres=concat $ map (\os-> case os of
                                          Op_name _->[]
                                          Qual_op_name _ ot _->
                                            case ot of
                                             Total_op_type args res _->[(args,res)]
                                             Partial_op_type args res _->[(args,res)]) ops
            iterateInhabited l =
	            if l==newL then newL else iterateInhabited newL
		             where newL =foldr (\ (as,rs) l'->
                                                  if (all (\s->elem s l') as)
                                                      && (not (elem rs l'))then rs:l'
					          else l') l argsAndres


inhabitedF :: FORMULA f -> [SORT]
inhabitedF f = case f of
                Sort_gen_ax constrs True-> inhabited constrs
                _ -> []
{- |

    Module      :  $Header$
    Description :  auxiliary functions on signatures and morphisms
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

    Maintainer  :  hets@informatik.uni-bremen.de
    Stability   :  provisional
    Portability :  portable

Auxiliary functions on signatures and morphisms
-}

module CASL.CCC.SignFuns where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

-- | Compute the image of a signature morphism

imageOfMorphism :: Morphism f e m  -> Sign f e
imageOfMorphism m =
        sig {sortSet = Rel.image sortMap (sortSet src),
             sortRel = Rel.map (\ a -> sortMap Map.! a ) (sortRel src),
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
              Nothing -> Map.insert ident (Set.singleton ot) opM
              Just ots -> Map.insert ident (Set.insert ot ots) opM
          pMap = pred_map m
          insertPred (ident,pt) predM =
            case Map.lookup ident predM of
              Nothing -> Map.insert ident (Set.singleton pt) predM
              Just pts -> Map.insert ident (Set.insert pt pts) predM


inhabited :: [SORT] -> [Constraint] -> [SORT]
inhabited sorts constrs = iterateInhabited sorts
    where (_,ops,_)=recover_Sort_gen_ax constrs
          argsRes=concat $
                    map (\os-> case os of
                                 Op_name _->[]
                                 Qual_op_name _ ot _->
                                     case ot of
                                       Op_type _ args res _ -> [(args,res)]
                        ) ops
          iterateInhabited l =
                    if l==newL then newL else iterateInhabited newL
                            where newL =foldr (\(ags,rs) l'->
                                                  if (all (\s->elem s l') ags)
                                                      && (not (elem rs l'))
                                                  then rs:l'
                                                  else l') l argsRes

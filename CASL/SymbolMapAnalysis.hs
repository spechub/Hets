
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
the symbol and morphism stuff for a logic

-}

module CASL.SymbolMapAnalysis where

import CASL.StaticAna
import CASL.Morphism
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.PrettyPrint


inducedFromMorphism :: Map.EndoMap RawSymbol -> Sign -> Result Morphism
inducedFromMorphism rmap sigma = do
  let syms = symOf sigma
      incorrectRsyms = Map.foldWithKey
        (\rsy _ -> if Set.any (\sy -> matches sy rsy) syms
                    then id
                    else Set.insert rsy)
        Set.empty
        rmap
  if Set.isEmpty incorrectRsyms then return ()
   else plain_error () 
          ("the following symbols: "++show incorrectRsyms++
           "do not match with signature "++showPretty sigma "")
          nullPos
  sortMap <- Set.fold 
              (\s m -> do s' <- sortFun s
                          m1 <- m
                          return $ Map.insert s s' m1) 
              (return Map.empty) sortsSigma
  let sigma' = 
        sigma {sortSet = Set.image (mapSort sortMap) sortsSigma}
      mor = Morphism { msource = sigma,
                   mtarget = sigma',
                   sort_map = sortMap,
                   fun_map = Map.empty,
                   pred_map = Map.empty }
  return mor
  where 
  sortsSigma = sortSet sigma
  sortFun s = 
    case Set.size rsys of
          0 -> return s
          1 -> return $ rawSymName $ Set.findMin rsys
          _ -> plain_error s 
                 ("Sort "++ showPretty s 
                   (" mapped ambiguously: "++show rsys)) 
                     -- ??? should become showPretty 
                 nullPos
    where
    rsys = Map.foldWithKey 
             (\rsy1 rsy2 set -> if (idToSortSymbol s) `matches` rsy1
                                 then Set.insert rsy2 set
                                 else set) 
             Set.empty rmap

inducedFromToMorphism :: Map.EndoMap RawSymbol
                         -> Sign -> Sign -> Result Morphism
inducedFromToMorphism rmap sigma1 sigma2 = do
  mor1 <- inducedFromMorphism rmap sigma1
  if isSubSig (mtarget mor1) sigma2 
   then return mor1
   else plain_error mor1 "true fitting maps nyi" nullPos
  
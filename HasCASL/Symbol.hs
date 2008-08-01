{- |
Module      :  $Header$
Description :  symbol analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

HasCASL analysed symbols of a signature
-}

module HasCASL.Symbol where

import HasCASL.Le
import HasCASL.PrintLe()
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.RawSym
import Common.Id
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set

instance GetRange Symbol where
    getRange = getRange . symName

checkSymbols :: SymbolSet -> SymbolSet -> Result a -> Result a
checkSymbols s1 s2 r =
    let s = foldr ( \ e2 d ->
                 Set.filter (not . matchSymb e2 . ASymbol) d)
                  s1 $ Set.toList s2 in
    if Set.null s then r else
       Result [mkDiag Error "unknown symbols" s] Nothing

dependentSyms :: Symbol -> Env -> SymbolSet
dependentSyms sym sig =
    Set.fold ( \ op se ->
               if Set.member sym $ subSymsOf op then
               Set.insert op se else se) Set.empty $ symOf sig

hideRelSymbol :: Symbol -> Env -> Env
hideRelSymbol sym sig =
    hideSymbol sym $ Set.fold hideSymbol sig $ dependentSyms sym sig


hideSymbol :: Symbol -> Env -> Env
hideSymbol sym sig =
    let i = symName sym
        tm = typeMap sig
        as = assumps sig in
    case symType sym of
    ClassAsItemType _ -> sig
    TypeAsItemType _ -> sig { typeMap =
                              Map.delete i tm }
    OpAsItemType ot ->
        let os = Map.findWithDefault Set.empty i as
            rs = Set.filter (not . (== ot) . opType) os
        in sig { assumps = if Set.null rs then Map.delete i as
                          else Map.insert i rs as }

plainHide :: SymbolSet -> Env -> Env
plainHide syms sigma =
    let (opSyms, otherSyms) = Set.partition (\ sy -> case symType sy of
                                              OpAsItemType _ -> True
                                              _ -> False) syms
    in Set.fold hideSymbol (Set.fold hideSymbol sigma otherSyms) opSyms

-- | type ids within a type
subSyms :: Env -> Type -> SymbolSet
subSyms e t = case t of
           TypeName i k n ->
               if n == 0 then if i == unitTypeId || i == lazyTypeId ||
                 isArrow i || isProductId i then Set.empty
                  else Set.singleton $ idToTypeSymbol e i k
               else Set.empty
           TypeAppl t1 t2 -> Set.union (subSyms e t1) (subSyms e t2)
           ExpandedType _ t1 -> subSyms e t1
           KindedType tk _ _ -> subSyms e tk
           TypeAbs _ b _ -> subSyms e b
           _ -> error ("subSyms: " ++ show t)

subSymsOf :: Symbol -> SymbolSet
subSymsOf sy = case symType sy of
     OpAsItemType (TypeScheme _ ty _) -> subSyms (symEnv sy) ty
     _ -> Set.empty

closeSymbSet :: SymbolSet -> SymbolSet
closeSymbSet s = Set.unions (s : map subSymsOf (Set.toList s))

symOf :: Env -> SymbolSet
symOf sigma =
    let classes = Map.foldWithKey ( \ i ks ->
                          Set.insert $ idToClassSymbol sigma i $ rawKind ks)
                  Set.empty $ classMap sigma
        types = Map.foldWithKey ( \ i ti ->
                        if Map.member i bTypes then id else
                        Set.insert $ idToTypeSymbol sigma i $ typeKind ti)
                classes $ typeMap sigma
        ops = Map.foldWithKey ( \ i ts s ->
                      if Map.member i bOps then s else
                      Set.fold ( \ t ->
                          Set.insert $ idToOpSymbol sigma i $ opType t) s ts)
              types $ assumps sigma
        in ops

{- |
Module      :  ./HasCASL/Symbol.hs
Description :  symbol analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

HasCASL analysed symbols of a signature
-}

module HasCASL.Symbol where

import HasCASL.Le
import HasCASL.PrintLe ()
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
    let s = foldr ( \ e2 ->
                 Set.filter (not . matchSymb e2 . ASymbol))
                  s1 $ Set.toList s2 in
    if Set.null s then r else
       Result [mkDiag Error "unknown HasCASL symbols" s] Nothing

dependentSyms :: Symbol -> Env -> SymbolSet
dependentSyms sym =
    Set.fold ( \ op se ->
               if Set.member sym $ subSymsOf op then
               Set.insert op se else se) Set.empty . Set.unions . symOf

hideRelSymbol :: Symbol -> Env -> Env
hideRelSymbol sym sig =
    hideSymbol sym $ Set.fold hideSymbol sig $ dependentSyms sym sig


hideSymbol :: Symbol -> Env -> Env
hideSymbol sym sig =
    let i = symName sym
        cm = classMap sig
        tm = typeMap sig
        as = assumps sig in
    case symType sym of
    ClassAsItemType _ -> sig
      { classMap = Map.map
        (\ ci -> ci { classKinds = Set.filter
                      (Set.notMember i . idsOfKind) $ classKinds ci })
        $ Map.delete i cm
      , typeMap = Map.map
        (\ ti -> ti { otherTypeKinds = Set.filter
                      (Set.notMember i . idsOfKind) $ otherTypeKinds ti })
        tm }
    TypeAsItemType _ -> sig
      { typeMap = Map.map
        (\ ti -> ti { superTypes = Set.delete i $ superTypes ti })
        $ Map.delete i tm }
    OpAsItemType ot ->
        let os = Map.findWithDefault Set.empty i as
            rs = Set.filter ((/= ot) . opType) os
        in sig { assumps = if Set.null rs then Map.delete i as
                          else Map.insert i rs as }
    _ -> sig

idsOfKind :: Kind -> Set.Set Id
idsOfKind kd = case kd of
  ClassKind i -> Set.singleton i
  FunKind _ k1 k2 _ -> Set.union (idsOfKind k1) $ idsOfKind k2

plainHide :: SymbolSet -> Env -> Env
plainHide syms sigma =
    let (opSyms, otherSyms) = Set.partition (\ sy -> case symType sy of
                                              OpAsItemType _ -> True
                                              _ -> False) syms
    in Set.fold hideSymbol (Set.fold hideSymbol sigma otherSyms) opSyms

-- | type ids within a type
subSyms :: Type -> SymbolSet
subSyms t = case t of
           TypeName i k n ->
               if n == 0 then if i == unitTypeId || i == lazyTypeId ||
                 isArrow i || isProductId i then Set.empty
                  else Set.singleton $ idToTypeSymbol i k
               else Set.empty
           TypeAppl t1 t2 -> Set.union (subSyms t1) (subSyms t2)
           ExpandedType _ t1 -> subSyms t1
           KindedType tk _ _ -> subSyms tk
           TypeAbs _ b _ -> subSyms b
           _ -> error ("subSyms: " ++ show t)

subSymsOf :: Symbol -> SymbolSet
subSymsOf sy = case symType sy of
     OpAsItemType (TypeScheme _ ty _) -> subSyms ty
     _ -> Set.empty

closeSymbSet :: SymbolSet -> SymbolSet
closeSymbSet s = Set.unions (s : map subSymsOf (Set.toList s))

opSymOf :: Env -> SymbolSet
opSymOf sigma = Map.foldrWithKey ( \ i ts s ->
                      if Map.member i bOps then s else
                      Set.fold (Set.insert . idToOpSymbol i . opType)
                         s ts)
              Set.empty $ assumps sigma

symOf :: Env -> [SymbolSet]
symOf sigma =
    let classes = Map.foldrWithKey ( \ i ->
                          Set.insert . idToClassSymbol i . rawKind)
                  Set.empty $ classMap sigma
        types = Map.foldrWithKey ( \ i ti ->
                        if Map.member i bTypes then id else
                        Set.insert $ idToTypeSymbol i $ typeKind ti)
                Set.empty $ typeMap sigma
        ops = Map.foldrWithKey ( \ i ts s ->
                      if Map.member i bOps then s else
                      Set.fold (Set.insert . idToOpSymbol i . opType)
                         s ts)
              Set.empty $ assumps sigma
        in [classes, types, ops]

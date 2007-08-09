{- |
Module      :  $Header$
Description :  compute subtype dependencies
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

compute subtype dependencies
-}

module HasCASL.TypeRel where

import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.ClassAna

typeRel :: TypeMap -> Rel.Rel Id
typeRel = Rel.irreflex . Rel.transClosure . Map.foldWithKey ( \ i ti r ->
    Set.fold (Rel.insert i) r $ superTypes ti) Rel.empty

getRawKind :: TypeMap -> Id -> RawKind
getRawKind tm i = typeKind $
    Map.findWithDefault (error $ showId i " not found in type map") i tm

-- | make injection (if True) or projection function
mkInjOrProj :: Bool -> TypeMap -> (Id, Id) -> OpInfo
mkInjOrProj b tm (i0, j0) = let
    (i, j) = if b then (i0, j0) else (j0, i0)
    k1 = getRawKind tm i
    k2 = getRawKind tm j
    (l1, l2, l3) = mkTypeArgs 1 k1 k2
 in if mapKindV (const InVar) id k1 == mapKindV (const InVar) id k2 then OpInfo
    { opType = TypeScheme l3 (mkFunArrType
          (patToType i l1 rStar)
          (if b then FunArr else PFunArr)
          $ patToType j l2 rStar) nullRange
    , opAttrs = Set.empty
    , opDefn = NoOpDefn Fun }
    else error "mkInjOrProj"

mkTypeArgs :: Int -> RawKind -> RawKind -> ([TypeArg], [TypeArg], [TypeArg])
mkTypeArgs i k1 k2 = case (k1, k2) of
    (ClassKind (), ClassKind ()) -> ([], [], [])
    (FunKind v1 a1 r1 _, FunKind v2 a2 r2 _) -> let
        (l1, l2, l3) = mkTypeArgs (i + 1) r1 r2
        mkTypeArg v k rk s = TypeArg (mkId [mkSimpleId (s ++ show i)]) v
            k rk (-i) Other nullRange
        in case (v1, v2) of
            (CoVar, CoVar) -> let
              t2 = mkTypeArg v2 (VarKind $ rawToKind a2) a2 "b"
              t1 = mkTypeArg v1 (Downset $ typeArgToType t2) a1 "a"
              in (t1 : l1, t2 : l2, t2 : t1 : l3)
            (ContraVar, ContraVar) -> let
              t1 = mkTypeArg v1 (VarKind $ rawToKind a1) a1 "a"
              t2 = mkTypeArg v2 (Downset $ typeArgToType t1) a2 "b"
              in (t1 : l1, t2 : l2, t1 : t2 : l3)
            _ -> let t1 = mkTypeArg InVar (VarKind $ rawToKind a1) a1 "a"
                 in (t1 : l1, t1 : l2, t1 : l3)
    _ -> error "mkTypeArgs"

{- |
Module      :  $Header$
Description :  renaming according to signature morphisms
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

rename symbols of terms according to a signature morphisms
-}

module HasCASL.MapTerm where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.FoldTerm
import Common.Id
import qualified Data.Set as Set

type Rename = ((Id, TypeScheme) -> (Id, TypeScheme), Type -> Type)

renameRec :: Rename -> MapRec
renameRec m = mapRec
   { foldQualVar = \ _ -> QualVar . mapVar (snd m)
   , foldQualOp = \ _ b (PolyId i as ps) sc tys qs ->
        let (i2, sc2) = fst m (i, sc)
            in QualOp b (PolyId i2 as ps) sc2 (map (snd m) tys) qs
   , foldTypedTerm = \ _ te q -> TypedTerm te q . snd m
   , foldQuantifiedTerm = \ _ q ->
       QuantifiedTerm q . map (mapGenVar $ snd m)
   , foldAsPattern = \ _ -> AsPattern . mapVar (snd m)
   , foldMixTypeTerm = \ _ q -> MixTypeTerm q . snd m }

mapTerm :: Rename -> Term -> Term
mapTerm = foldTerm . renameRec

mapEq :: Rename -> ProgEq -> ProgEq
mapEq = foldEq . renameRec

mapVar :: (Type -> Type) -> VarDecl -> VarDecl
mapVar m (VarDecl v ty q ps) = VarDecl v (m ty) q ps

mapGenVar :: (Type -> Type) -> GenVarDecl -> GenVarDecl
mapGenVar m g = case g of
    GenVarDecl vd -> GenVarDecl $ mapVar m vd
    GenTypeVarDecl (TypeArg i v vk rk c s r) -> GenTypeVarDecl
      $ TypeArg i v (case vk of
          VarKind k -> -- extract kind renaming from type renaming
              let KindedType _ nk _ =
                      m $ KindedType unitType (Set.singleton k) r
              in VarKind $ Set.findMin nk
          Downset t -> Downset $ m t
          _ -> vk) rk c s r

mapOpInfo :: Rename -> OpInfo -> OpInfo
mapOpInfo m oi = oi
    { opType = mapTypeOfScheme (snd m) $ opType oi
    , opAttrs = Set.map (mapOpAttr m) $ opAttrs oi
    , opDefn = renameOpDefn m $ opDefn oi }

mapOpAttr :: Rename -> OpAttr -> OpAttr
mapOpAttr m o = case o of
    UnitOpAttr t p -> UnitOpAttr (mapTerm m t) p
    _ -> o

renameOpDefn :: Rename -> OpDefn -> OpDefn
renameOpDefn m d = case d of
    SelectData cs i -> SelectData (Set.map (renameConstrInfo $ snd m) cs) i
    Definition b t -> Definition b $ mapTerm m t
    _ -> d

renameConstrInfo :: (Type -> Type) -> ConstrInfo -> ConstrInfo
renameConstrInfo m c = c { constrType = mapTypeOfScheme m $ constrType c }

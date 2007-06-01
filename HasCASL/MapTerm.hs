{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

rename symbols of terms according to a signature morphisms
-}

module HasCASL.MapTerm where

import HasCASL.As
import HasCASL.Le
import HasCASL.FoldTerm
import Common.Id

type Rename = ((Id, TypeScheme) -> (Id, TypeScheme), Type -> Type)

renameRec :: Rename -> MapRec
renameRec m = mapRec
   { foldQualVar = \ _ vd -> QualVar $ mapVar (snd m) vd
   , foldQualOp = \ _ b (InstOpId i ts ps) sc qs ->
        let (i2, sc2) = fst m (i, sc)
            in QualOp b (InstOpId i2 (map (snd m) ts) ps) sc2 qs
   , foldTypedTerm = \ _ te q ty ps -> TypedTerm te q (snd m ty) ps
   , foldQuantifiedTerm = \ _ q vs te ps ->
       QuantifiedTerm q (map (mapGenVar $ snd m) vs) te ps
   , foldAsPattern = \ _ vd pa ps -> AsPattern (mapVar (snd m) vd) pa ps
   , foldMixTypeTerm = \ _ q ty ps -> MixTypeTerm q (snd m ty) ps }

mapTerm :: Rename -> Term -> Term
mapTerm m = foldTerm $ renameRec m

mapEq :: Rename -> ProgEq -> ProgEq
mapEq m = foldEq $ renameRec m

mapVar :: (Type -> Type) -> VarDecl -> VarDecl
mapVar m (VarDecl v ty q ps) = VarDecl v (m ty) q ps

mapGenVar :: (Type -> Type) -> GenVarDecl -> GenVarDecl
mapGenVar m g = case g of
    GenVarDecl vd -> GenVarDecl $ mapVar m vd
    _ -> g

mapOpInfo :: Rename -> OpInfo -> OpInfo
mapOpInfo m oi = oi
    { opType = mapTypeOfScheme (snd m) $ opType oi
    , opAttrs = map (mapOpAttr m) $ opAttrs oi
    , opDefn = renameOpDefn m $ opDefn oi }

mapOpAttr :: Rename -> OpAttr -> OpAttr
mapOpAttr m o = case o of
    UnitOpAttr t p -> UnitOpAttr (mapTerm m t) p
    _ -> o

renameOpDefn :: Rename -> OpDefn -> OpDefn
renameOpDefn m d = case d of
    SelectData cs i -> SelectData (map (renameConstrInfo $ snd m) cs) i
    Definition b t -> Definition b $ mapTerm m t
    _ -> d

renameConstrInfo :: (Type -> Type) -> ConstrInfo -> ConstrInfo
renameConstrInfo m c = c { constrType = mapTypeOfScheme m $ constrType c }

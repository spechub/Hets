{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    
rename symbols of terms according to a signature morphisms

-}

module HasCASL.MapTerm where

import HasCASL.As
import HasCASL.Le
import Common.Id

type Rename = ((Id, TypeScheme) -> (Id, TypeScheme), Type -> Type)

mapTerm :: Rename -> Term -> Term
mapTerm m t = case t of
   QualVar vd -> QualVar $ mapVar (snd m) vd
   QualOp b (InstOpId i ts ps) sc qs -> 
        let (i2, sc2) = fst m (i, sc)
	    in QualOp b (InstOpId i2 (map (snd m) ts) ps) sc2 qs
   ApplTerm t1 t2 ps ->
       ApplTerm (mapTerm m t1) (mapTerm m t2) ps
   TupleTerm ts ps -> TupleTerm (map (mapTerm m) ts) ps
   TypedTerm te q ty ps -> TypedTerm (mapTerm m te) q (snd m ty) ps
   QuantifiedTerm q vs te ps -> 
       QuantifiedTerm q (map (mapGenVar $ snd m) vs) (mapTerm m te) ps
   LambdaTerm ps p te qs ->     
       LambdaTerm (map (mapTerm m) ps) p (mapTerm m te) qs
   CaseTerm te es ps -> 
       CaseTerm (mapTerm m te) (map (mapEq m) es) ps
   LetTerm b es te ps ->
       LetTerm b (map (mapEq m) es) (mapTerm m te) ps
   AsPattern vd pa ps -> AsPattern (mapVar (snd m) vd) (mapTerm m pa) ps
   TermToken _ -> t
   MixfixTerm ts -> MixfixTerm $ map (mapTerm m) ts
   BracketTerm b ts ps -> BracketTerm b (map (mapTerm m) ts) ps
   MixTypeTerm q ty ps -> MixTypeTerm q (snd m ty) ps  
   ResolvedMixTerm i ts ps -> ResolvedMixTerm i (map (mapTerm m) ts) ps

mapGenVar :: (Type -> Type) -> GenVarDecl -> GenVarDecl
mapGenVar m (GenVarDecl vd) = GenVarDecl $ mapVar m vd
mapGenVar _ tv = tv 

mapVar :: (Type -> Type) -> VarDecl -> VarDecl
mapVar m (VarDecl v ty q ps) = VarDecl v (m ty) q ps

mapEq :: Rename -> ProgEq -> ProgEq
mapEq m (ProgEq p t ps) = ProgEq (mapTerm m p) (mapTerm m t) ps

mapOpInfo :: Rename -> OpInfo -> OpInfo
mapOpInfo m oi = oi { opType = mapTypeOfScheme (snd m) $ opType oi
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


{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
rename symbols of terms according to a signature morphisms

-}

module HasCASL.MapTerm where

import HasCASL.As
import Common.Id

mapTerm :: ((Id, TypeScheme) -> (Id, TypeScheme), Type -> Type) -> Term -> Term
mapTerm m t = case t of
   QualVar v ty ps -> QualVar v (snd m ty) ps
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
   AsPattern v pa ps -> AsPattern v (mapTerm m pa) ps
   _ -> error "mapTerm"

mapGenVar :: (Type -> Type) -> GenVarDecl -> GenVarDecl
mapGenVar m (GenVarDecl vd) = GenVarDecl $ mapVar m vd
mapGenVar _ tv = tv 

mapVar :: (Type -> Type) -> VarDecl -> VarDecl
mapVar m (VarDecl v ty q ps) = VarDecl v (m ty) q ps

mapEq :: ((Id, TypeScheme) -> (Id, TypeScheme), Type -> Type) 
      -> ProgEq -> ProgEq
mapEq m (ProgEq p t ps) = ProgEq (mapTerm m p) (mapTerm m t) ps

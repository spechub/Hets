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

import HasCASL.Morphism
import HasCASL.As
import HasCASL.Symbol
import Common.Result
import qualified Common.Lib.Map as Map

mapTp :: Morphism -> Type -> Type
mapTp m = mapType $ typeIdMap m

mapSen :: Morphism -> Term -> Result Term
mapSen m t = return $ mapTerm m t

mapTerm :: Morphism -> Term -> Term
mapTerm m t = case t of
   QualVar v ty ps -> QualVar v (mapTp m ty) ps
   QualOp b (InstOpId i ts ps) sc qs -> 
        let (i2, TySc sc2) = Map.findWithDefault 
			     (i, TySc $ mapTypeScheme (typeIdMap m) sc) 
			     (i, TySc sc) $ funMap m
	    in QualOp b (InstOpId i2 (map (mapTp m) ts) ps) sc2 qs
   ApplTerm t1 t2 ps ->
       ApplTerm (mapTerm m t1) (mapTerm m t2) ps
   TupleTerm ts ps -> TupleTerm (map (mapTerm m) ts) ps
   TypedTerm te q ty ps -> TypedTerm (mapTerm m te) q (mapTp m ty) ps
   QuantifiedTerm q vs te ps -> 
       QuantifiedTerm q (map (mapGenVar m) vs) (mapTerm m te) ps
   LambdaTerm ps p te qs ->     
       LambdaTerm (map (mapPat m) ps) p (mapTerm m te) qs
   CaseTerm te es ps -> 
       CaseTerm (mapTerm m te) (map (mapEq m) es) ps
   LetTerm b es te ps ->
       LetTerm b (map (mapEq m) es) (mapTerm m te) ps
   _ -> error "mapTerm"

mapGenVar :: Morphism -> GenVarDecl -> GenVarDecl
mapGenVar m (GenVarDecl vd) = GenVarDecl $ mapVar m vd
mapGenVar _ tv = tv 

mapVar :: Morphism -> VarDecl -> VarDecl
mapVar m (VarDecl v ty q ps) = VarDecl v (mapTp m ty) q ps

mapEq :: Morphism -> ProgEq -> ProgEq
mapEq m (ProgEq p t ps) = ProgEq (mapPat m p) (mapTerm m t) ps

mapPat ::  Morphism -> Pattern -> Pattern
mapPat m p = case p of
   PatternVar vd -> PatternVar $ mapVar m vd
   PatternConstr (InstOpId i ts ps) sc qs ->
       let (i2, TySc sc2) = Map.findWithDefault 
			    (i, TySc $ mapTypeScheme (typeIdMap m) sc) 
			    (i, TySc sc) $ funMap m
	    in PatternConstr (InstOpId i2 (map (mapTp m) ts) ps) sc2 qs
   ApplPattern p1 p2 ps -> ApplPattern (mapPat m p1) (mapPat m p2) ps
   TuplePattern ps qs -> TuplePattern (map (mapPat m) ps) qs
   TypedPattern pa ty ps -> TypedPattern (mapPat m pa) (mapTp m ty) ps
   AsPattern v pa ps -> AsPattern v (mapPat m pa) ps
   _ -> error "mapPat"

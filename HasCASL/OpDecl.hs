{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse operation declarations
-}

module HasCASL.OpDecl where

import HasCASL.As
import HasCASL.VarDecl
import HasCASL.Le
import Common.Lib.State
import Common.Result
import Common.GlobalAnnotations
import HasCASL.Unify
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.MixAna
import Data.Maybe

anaAttr :: GlobalAnnos -> TypeScheme -> OpAttr -> State Env (Maybe OpAttr)
anaAttr ga (TypeScheme tvs (_ :=> ty) _) (UnitOpAttr trm ps) = 
    do let mTy = case ty of 
		      FunType (ProductType [t1, t2] _) _ t3 _ -> 
			  Just (t1,t2,t3)
		      FunType t1 _ (FunType t2 _ t3 _) _ -> 
			  Just (t1,t2,t3)
		      _ -> Nothing
       tm <- gets typeMap
       mapM_ addTypeVarDecl tvs
       case mTy of 
	     Nothing -> do addDiags [mkDiag Error 
				     "unexpected type of operation" ty]
			   mt <- resolve ga Nothing trm
			   putTypeMap tm
			   case mt of 
				   Nothing -> return Nothing
				   Just (_, t) 
				       -> return $ Just $ UnitOpAttr t ps
	     Just (t1, t2, t3) -> 
		 do if t1 == t2 && t2 == t3 then
		       return ()
		       else addDiags [mkDiag Error 
				     "unexpected type of operation" ty]
                    mt <- resolveTerm ga t3 trm
		    putTypeMap tm
		    case mt of Nothing -> return Nothing
	                       Just t -> return $ Just $ UnitOpAttr t ps
anaAttr _ _ b = return $ Just b

filterVars :: Assumps -> Assumps
filterVars = filterAssumps (not . isVarDefn)

patternsToType :: [Pattern] -> Type -> Type
patternsToType [] t = t
patternsToType (p: ps) t = FunType (tuplePatternToType p) PFunArr 
			  (patternsToType ps t) []

tuplePatternToType :: Pattern -> Type
tuplePatternToType (PatternVar (VarDecl _ t _ _)) = t
tuplePatternToType (TuplePattern ps qs) = 
    ProductType (map tuplePatternToType ps) qs
tuplePatternToType _ = error "tuplePatternToType"

anaOpItem :: GlobalAnnos -> OpItem -> State Env OpItem
anaOpItem ga (OpDecl is sc attr ps) = 
    do mSc <- anaTypeScheme sc
       let nSc = case mSc of 
			  Nothing -> sc
			  Just s -> s 
       mAttrs <- mapM (anaAttr ga nSc) attr
       us <- mapM (anaOpId nSc attr) is
       return $ OpDecl (catMaybes us) nSc (catMaybes mAttrs) ps

anaOpItem ga (OpDefn o pats sc partial trm ps) = 
    do let (op@(OpId i _ _), extSc) = getUninstOpId sc o
	   bs = concatMap extractBindings pats
       mSc <- anaTypeScheme extSc 
       as <- gets assumps
       checkUniqueVars bs
       putAssumps $ filterVars as
       mapM_ anaVarDecl bs
       case mSc of 
		Just newSc@(TypeScheme tArgs (qu :=> _) qs) -> do 
		    ty <- toEnvState $ freshInst newSc
		    mt <- resolve ga (Just ty) trm
		    putAssumps as
		    case mt of 
			      Nothing -> return $ OpDefn op pats 
					     newSc partial trm ps
			      Just (newTy, lastTrm) -> do 
			          let lastSc = TypeScheme tArgs 
					  (qu :=> patternsToType pats newTy) qs
				  addOpId i lastSc [] $ Definition 
				         $ case (pats, partial) of 
					       ([], Total) -> lastTrm
					       _ -> LambdaTerm pats partial 
						    lastTrm ps
				  return $ OpDefn op [] lastSc
					   partial lastTrm ps
		Nothing -> do 
		    mt <- resolve ga Nothing trm
		    putAssumps as
		    return $ OpDefn op pats extSc partial 
			      (case mt of Nothing -> trm
			                  Just (_, x) -> x) ps
							  

getUninstOpId :: TypeScheme -> OpId -> (OpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args qs) =
      (OpId i [] qs, TypeScheme (args ++ tvs) q ps)  

anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env (Maybe OpId) 
anaOpId sc attrs o =
    do let (OpId i _ _, newSc) = getUninstOpId sc o
       mo <- addOpId i newSc attrs NoOpDefn
       return $ fmap (const o) mo

anaTypeScheme :: TypeScheme -> State Env (Maybe TypeScheme)
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- gets typeMap    -- save global variables  
       mArgs <- mapM anaTypeVarDecl tArgs
       let newArgs = catMaybes mArgs  
       addDiags $ checkUniqueness
		       $ map (\ (TypeArg v _ _ _) -> v) newArgs
       mt <- anaStarType ty
       putTypeMap tm       -- forget local variables 
       case mt of 
           Nothing -> return Nothing
	   Just newTy -> return $ Just $ TypeScheme newArgs (q :=> newTy) p

-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env ProgEq
anaProgEq ga pe@(ProgEq pat trm qs) =
    do as <- gets assumps
       putAssumps $ filterVars as
       mp <- resolveTargetPattern ga Nothing pat
       let exbs = case mp of 
			Nothing -> []
			Just (_, newPat) -> extractBindings newPat
       checkUniqueVars exbs
       mapM_ addVarDecl exbs
       mt <- resolve ga (fmap fst mp) trm
       putAssumps as
       case (mt, mp) of 
	    (Just (_, newTerm), Just (_, newPat))  ->
		case removeResultType newPat of
		       PatternConstr (InstOpId i _tys _) sc args ps ->
			   do addOpId i sc [] $ Definition $ 
			          if null args then newTerm
				     else LambdaTerm args Partial newTerm ps
			      return $ ProgEq newPat newTerm qs
		       _ -> do addDiags $ [mkDiag Error 
					   "no toplevel pattern" newPat]
			       return pe
		       where removeResultType p = 
				 case p of 
				 TypedPattern tp _ _ -> tp
				 _ -> p
	    _ -> return pe


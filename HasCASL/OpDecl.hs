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

anaOpItem :: GlobalAnnos -> OpItem -> State Env ()
anaOpItem _ (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem ga (OpDefn o pats sc partial trm ps) = 
    do let newTrm = if null pats then trm else 
		 LambdaTerm pats partial trm ps 
       (i, mSc) <- getUninstOpId sc o
       case mSc of 
           Nothing -> do resolveAny ga newTrm
			 return ()
	   Just newSc -> do 
	       ty <- toEnvState $ freshInst newSc
	       mt <- resolveTerm ga ty newTrm
	       case mt of 
	           Nothing -> return ()
		   Just lastTrm -> do addOpId i newSc [] $ Definition lastTrm
				      return ()

getUninstOpId :: TypeScheme -> OpId -> State Env (UninstOpId, Maybe TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args _) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       addDiags $ checkUniqueness
		       $ map (\ (TypeArg v _ _ _) -> v) newArgs
       newSc <- anaTypeScheme sc
       return (i, newSc)


anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env ()
anaOpId sc attrs o =
    do (i, mSc) <- getUninstOpId sc o
       case mSc of 
           Nothing -> return () 
	   Just newSc -> do addOpId i newSc attrs NoOpDefn
			    return ()

anaTypeScheme :: TypeScheme -> State Env (Maybe TypeScheme)
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       mt <- anaStarType ty
       putTypeMap tm       -- forget local variables 
       case mt of 
           Nothing -> return Nothing
	   Just newTy -> return $ Just $ TypeScheme tArgs (q :=> newTy) p

-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env ()
anaProgEq ga (ProgEq pat trm _) =
    do mp <- resolvePattern ga pat
       case mp of 
	   Nothing -> return ()
	   Just (ty, newPat) -> do
	       let bs = extractBindings newPat
	       e <- get
	       mapM_ anaVarDecl bs
	       mt <- resolveTerm ga ty trm
	       put e
	       case mt of 
		   Nothing -> return ()
		   Just newTerm ->case removeResultType newPat of
		       PatternConstr (InstOpId i _tys _) sc args ps ->
			   do addOpId i sc [] $ Definition $ 
			          if null args then newTerm
				     else LambdaTerm args Partial newTerm ps
			      return ()
		       _ -> addDiags $ [mkDiag Error 
					   "no toplevel pattern" newPat]
		       where removeResultType p = 
				 case p of 
				 TypedPattern tp _ _ -> 
				     removeResultType tp
				 _ -> p


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
import HasCASL.TypeDecl
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
       (i, newSc) <- getUninstOpId sc o
       ty <- toEnvState $ freshInst newSc
       mt <- resolveTerm ga ty newTrm
       case mt of 
	       Nothing -> return ()
	       Just lastTrm -> addOpId i newSc [] $ Definition lastTrm

getUninstOpId :: TypeScheme -> OpId -> State Env (UninstOpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args _) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       addDiags $ checkUniqueness
		       $ map (\ (TypeArg v _ _ _) -> v) newArgs
       newSc <- anaTypeScheme sc
       return (i, newSc)


anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env ()
anaOpId sc attrs o =
    do (i, newSc) <- getUninstOpId sc o
       addOpId i newSc attrs NoOpDefn

anaTypeScheme :: TypeScheme -> State Env TypeScheme
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       newTy <- anaStarType ty
       let newPty = TypeScheme tArgs (q :=> newTy) p
       putTypeMap tm       -- forget local variables 
       return newPty

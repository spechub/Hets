
{- HetCATS/HasCASL/OpDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse op decls
-}

module HasCASL.OpDecl where

import HasCASL.As
import HasCASL.ClassDecl
import HasCASL.TypeDecl
import HasCASL.Le
import Common.Lib.State
import Common.Result
import HasCASL.Unify
import HasCASL.MixAna

anaOpItem :: OpItem -> State Env ()
anaOpItem (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem (OpDefn o pats sc partial trm ps) = 
    do let newTrm = if null pats then trm else 
		 LambdaTerm pats partial trm ps 
       (i, newSc) <- getUninstOpId sc o
       ty <- toEnvState $ freshInst newSc
       Result ds mt <- resolveTermWithType (Just ty) newTrm
       appendDiags ds 
       case mt of 
	       Just t -> addOpId i newSc [] $ Definition t
	       _ -> return ()

getUninstOpId :: TypeScheme -> OpId -> State Env (UninstOpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args _) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       appendDiags $ checkUniqueness
		       $ map (\ (TypeArg v _ _ _) -> v) newArgs
       (k, newSc) <- anaTypeScheme sc
       checkKindsS i star k
       return (i, newSc)


anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env ()
anaOpId sc attrs o =
    do (i, newSc) <- getUninstOpId sc o
       addOpId i newSc attrs NoOpDefn

anaTypeScheme :: TypeScheme -> State Env (Kind, TypeScheme)
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       (ik, newTy) <- anaTypeS (star, ty)
       let newPty = TypeScheme tArgs (q :=> newTy) p
       putTypeMap tm       -- forget local variables 
       return (ik, newPty)


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
import HasCASL.ClassDecl
import HasCASL.TypeDecl
import HasCASL.Le
import Common.Lib.State
import Common.Result
import Common.GlobalAnnotations
import HasCASL.Unify
import HasCASL.MixAna

anaOpItem :: GlobalAnnos -> OpItem -> State Env ()
anaOpItem _ (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem ga (OpDefn o pats sc partial trm ps) = 
    do let newTrm = if null pats then trm else 
		 LambdaTerm pats partial trm ps 
       (i, newSc) <- getUninstOpId sc o
       ty <- toEnvState $ freshInst newSc
       Result ds mt <- toRResultState $ resolveTerm ga ty newTrm
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

getArgsRes :: Type -> [a] -> ([Type], Type)
getArgsRes t [] = ([], t)
getArgsRes (FunType t1 _ t2 _) (a:r) = 
    let (as, res) = getArgsRes t2 r in
		    (t1:as, res)
getArgsRes _ _ = error "getArgsRes"


{- 
specializePatVars :: TypeMap -> (Type, Pattern) 
		  -> RState Int Subst
specializePatVars tm (ty, pat) = 
    case pat of 
    PatternVar (VarDecl v vty k ps) 
        -> liftR $ unify tm ty vty 
    PatternConstr i sc args ps
        -> do ity <- freshInst sc
	      let (ats, res) = getArgsRes ity args
	      s <- liftR $ unify tm ty res
	      largs <- mapM specializePatVars 
		   newts = map (subst s) ats

	      
InstOpId TypeScheme [Pattern] [Pos] 
	     -- constructor or toplevel operation applied to arguments
	     -- pos "("s, ")"s
             | PatternToken Token
	     | BracketPattern BracketKind [Pattern] [Pos]
	     -- pos brackets, ";"s, ","s
	     | TuplePattern [Pattern] [Pos]
	     -- pos ","s
	     | MixfixPattern [Pattern] -- or HO-Pattern
	     | TypedPattern Pattern Type [Pos]	     -- pos ":"  
	     | AsPattern Pattern Pattern [Pos]
         TypePattern 
-}


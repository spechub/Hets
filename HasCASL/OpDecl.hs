
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
import Common.Id
import HasCASL.Le
import Common.Lib.State
import Common.Lib.Parsec.Pos
import qualified Common.Lib.Map as Map
import Common.Result
import Data.List
import Data.Maybe
import HasCASL.Unify
import HasCASL.MixAna

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }

posOfOpId :: OpId -> Pos
posOfOpId (OpId i _ _) = posOfId i

anaOpItem :: OpItem -> State Env ()
anaOpItem (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem (OpDefn o pats sc partial trm ps) = 
    do let newTrm = if null pats then trm else 
		 LambdaTerm pats partial trm ps 
       (i, newSc) <- getUninstOpId sc o
       Result ds mt <- resolveTerm newTrm
       appendDiags ds 
       case mt of 
	       Just t -> addOpId i newSc [] $ Definition t
	       _ -> return ()

getUninstOpId :: TypeScheme -> OpId -> State Env (UninstOpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args _) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       appendDiags $ checkDifferentTypeArgs newArgs
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

checkDifferentTypeArgs :: [TypeArg] -> [Diagnosis]
checkDifferentTypeArgs l = 
    let v = map (\ (TypeArg i _ _ _) -> i) l
	vd = filter ( not . null . tail) $ group $ sort v
    in map ( \ vs -> mkDiag Error ("duplicate ids at '" ++
	                          showSepList (showString " ") shortPosShow
				  (map posOfId (tail vs)) "'" 
				   ++ " for")  (head vs)) vd

shortPosShow :: Pos -> ShowS
shortPosShow p = showParen True (shows (sourceLine p) . showString "," .
			 shows (sourceColumn p))

unifiable :: TypeScheme -> TypeScheme -> State Env Bool
unifiable sc1 sc2 =
    do tm <- gets typeMap
       c <- gets counter
       let Result ds mm = evalState (unifIable tm sc1 sc2) c
       appendDiags ds
       return $ isJust mm

addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn -> State Env () 
addOpId i sc attrs defn = 
    do as <- gets assumps
       let l = Map.findWithDefault [] i as
       if sc `elem` map opType l then 
	  addDiag $ mkDiag Warning 
		      "repeated value" i
	  else do bs <- mapM (unifiable sc) $ map opType l
		  if or bs then addDiag $ mkDiag Error
			 "illegal overloading of" i
	             else putAssumps $ Map.insert i 
			      (OpInfo sc attrs defn : l ) as

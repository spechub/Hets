
{- HetCATS/HasCASL/OpDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse op decls
-}

module HasCASL.OpDecl where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ClassAna
import HasCASL.TypeAna
import Common.Id
import HasCASL.Le
import Control.Monad.State
import Common.PrettyPrint
import HasCASL.PrintAs(showPretty)
import Common.Lib.Parsec.Pos
import qualified Common.Lib.Map as Map
import Common.Result
import HasCASL.TypeDecl
import Data.List

missingAna :: PrettyPrint a => a -> [Pos] -> State Env ()
missingAna t ps = appendDiags [Diag FatalError 
			       ("no analysis yet for: " ++ showPretty t "")
			      $ if null ps then nullPos else head ps]

posOfOpId :: OpId -> Pos
posOfOpId (OpId i _ _) = posOfId i

anaOpItem :: OpItem -> State Env ()
anaOpItem (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem (OpDefn i _ _ _ _ _) = missingAna i [posOfOpId i]

anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env ()
anaOpId (TypeScheme tvs q ps) attrs (OpId i args _) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       appendDiags $ checkDifferentTypeArgs newArgs
       (mk, newSc) <- anaTypeScheme sc
       case mk of 
	       Nothing -> return () -- induced error
	       Just k -> do checkKinds (posOfId i) k star
			    addOpId i newSc attrs

anaTypeScheme :: TypeScheme -> State Env (Maybe Kind, TypeScheme)
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- getTypeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       (ik, newTy) <- anaType ty
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

addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> State Env () 
addOpId i sc attrs = missingAna i [posOfId i]

{-
unifiable :: TypeScheme -> TypeScheme -> State Env 
unifiable sc1 sc2 =
    do t1 <- freshInst sc1
       t2 <- freshInst sc2
       unify t1 t2

freshInst (TypeScheme tArgs (q :=> t) _) = 
    do i <- getState
       setState (i + length tArgs)
       return $ subst (mkSubst tArgs i) t 
-}
type Subst = Map.Map TypeId Type

mkSubst :: [TypeArg] -> Integer -> Subst
mkSubst [] _ = Map.empty
mkSubst (TypeArg v _ _ _:r) i =
     let tId = simpleIdToId $ mkSimpleId ("_var_" ++ show i)
     in Map.insert v (TypeName tId 0) $ mkSubst r (i+1) 
 		   

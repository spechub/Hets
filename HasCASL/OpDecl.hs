
{- HetCATS/HasCASL/OpDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse op decls
-}

module HasCASL.OpDecl where

import HasCASL.As
import HasCASL.ClassAna
import HasCASL.TypeAna
import Common.Id
import HasCASL.Le
import Control.Monad.State
import Common.PrettyPrint
import HasCASL.PrintAs()
import Common.Lib.Parsec.Pos
import qualified Common.Lib.Map as Map
import Common.Result
import HasCASL.TypeDecl
import Data.List
import Data.Maybe
import HasCASL.Unify


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
			    addOpId i newSc attrs NoOpDefn

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

addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn -> State Env () 
addOpId i sc attrs defn = 
    do as <- getAssumps
       let l = Map.findWithDefault [] i as
       if sc `elem` map opType l then 
	  addDiag $ mkDiag Warning 
		      "repeated value" i
	  else do bs <- mapM (unifiable sc) $ map opType l
		  if or bs then addDiag $ mkDiag Error
			 "illegal overloading of" i
	             else putAssumps $ Map.insert i 
			      (OpInfo sc attrs defn : l ) as

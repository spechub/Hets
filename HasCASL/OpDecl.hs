
{- HetCATS/HasCASL/OpDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse op decls
-}

module OpDecl where

import As
import AsUtils
import ClassAna
import FiniteMap
import Id
import Le
import Control.Monad.State
import PrettyPrint
import PrintAs(showPretty)
import Common.Lib.Parsec.Pos
import Result
import TypeDecl
import Data.List

missingAna :: PrettyPrint a => a -> [Pos] -> State Env ()
missingAna t ps = appendDiags [Diag FatalError 
			       ("no analysis yet for: " ++ showPretty t "")
			      $ if null ps then nullPos else head ps]

posOfOpId :: OpId -> Pos
posOfOpId (OpId i _) = posOfId i

anaOpItem :: OpItem -> State Env ()
anaOpItem (OpDecl is sc attr _) = 
    mapM_ (anaOpId sc attr) is

anaOpItem (OpDefn i _ _ _ _ _) = missingAna i [posOfOpId i]

anaOpId :: TypeScheme -> [OpAttr] -> OpId -> State Env ()
anaOpId (TypeScheme tvs q ps) attrs (OpId i args) =
    do let newArgs = args ++ tvs
           sc = TypeScheme newArgs q ps
       appendDiags $ checkDifferentTypeArgs newArgs
       (mk, newSc) <- anaTypeScheme Nothing sc
       case mk of 
	       Nothing -> return () -- induced error
	       Just k -> if eqKind Compatible k star then
			 addOpId i newSc attrs
			 else addDiag $ mkDiag Error 
			      ("wrong kind '" ++ showPretty k
			       "' of type for operation") i 

checkDifferentTypeArgs :: [TypeArgs] -> [Diagnosis]
checkDifferentTypeArgs l = 
    let v :: [Id] = concatMap (\ (TypeArgs tas _) 
			       -> map (\ (TypeArg i _ _ _) -> i) tas) l
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

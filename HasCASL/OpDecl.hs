
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
import MonadState
import PrettyPrint
import PrintAs(showPretty)
import Result
import TypeDecl

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
    do let sc = TypeScheme (args ++ tvs) q ps 
       (mk, newSc) <- anaTypeScheme Nothing sc
       case mk of 
	       Nothing -> return () -- induced error
	       Just k -> if eqKind Compatible k star then
			 addOpId i newSc attrs
			 else addDiag $ mkDiag Error 
			      ("wrong kind '" ++ showPretty k
			       "' of type for operation") i 

addOpId i sc attrs = return () 

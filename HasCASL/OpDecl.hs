
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
import PrintAs(showPretty)
import Result
import TypeDecl


posOfOpId :: OpId -> Pos
posOfOpId (OpId i _) = posOfId i

anaOpItem :: OpItem -> State Env ()
anaOpItem (OpDecl is sc _ _) = let i = head is in 
				   missingAna i [posOfOpId i]
anaOpItem (OpDefn i _ _ _ _ _) = missingAna i [posOfOpId i]

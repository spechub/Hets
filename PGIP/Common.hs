{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Usefull function used by the parser.


   TODO 
       - add comment.

-} 

module PGIP.Common where
                      

import PGIP.Commands
import Proofs.EdgeUtils



-- | The 'addOrReplace' function,given a CmdInterpeterStatus and a list of such CmdInterpeterStatus, replaces any occurance of that type
-- of CmdInterpeterStatus with the given one, and if none found it adds one to the list
addOrReplace::([CmdInterpreterStatus],[CmdInterpreterStatus])->[CmdInterpreterStatus]
addOrReplace (val,status)
                      = case val of
                                  []                  ->  status
                                  (Env x y):l         -> case status of
                                                          []                    -> addOrReplace(l,(Env x y):[])
                                                          CmdInitialState:ls    -> addOrReplace ((Env x y):l,ls)
                                                          (OutputErr xx):_      -> (OutputErr xx):[]
                                                          (Env _ _):ls          -> addOrReplace(l,(Env x y):ls)
                                                          (SelectedNodes xx):ls -> addOrReplace(l, (SelectedNodes xx):addOrReplace([Env x y],ls))
                                  (SelectedNodes x):l -> case status of
                                                          []                    -> addOrReplace (l,(SelectedNodes x):[])
                                                          CmdInitialState:ls    -> addOrReplace ((SelectedNodes x):l, ls)
                                                          (OutputErr xx):_      -> (OutputErr xx):[]
                                                          (Env xx yy):ls        -> addOrReplace(l, (Env xx yy):addOrReplace([SelectedNodes x], ls))
                                                          (SelectedNodes _):ls  -> addOrReplace(l, (SelectedNodes x):ls)
                                  (OutputErr x):l -> (OutputErr x):[]
                                  CmdInitialState:l -> addOrReplace (l,status)

-- | The 'extractFrom' function, given a list of CmdInterpeterStatus and a CmdInterpreterStatusID, it returns the first occurance of 
-- that type of CmdInterpreterStatus from the list 
extractFrom::([CmdInterpreterStatus],CmdInterpreterStatusID) -> Maybe CmdInterpreterStatus
extractFrom (status,cmdID)
                          = case cmdID of
                                        EnvID -> do 
                                                   case status of 
                                                                [] -> Nothing
                                                                (Env x y):_ -> Just (Env x y)
                                                                _:ls-> (extractFrom (ls,cmdID))


-- | The 'extractNodeGoals' function, given a list of parsed goals extracts the NodeGoals as a list of LIB_ID's
--extractNodeGoals::[GOAL] -> [Id]
--extractNodeGoals ls
--                    = case ls of
--                                []          -> []
--                                (Node x):l  -> x:(extractNodeGoals l)
--                                _:l         -> extractNode l


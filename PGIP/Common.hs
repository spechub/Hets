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
-- | The 'addOrReplace' function,given a CmdInterpeterStatus and a list of such CmdInterpeterStatus, replaces any occurance of that type
-- of CmdInterpeterStatus with the given one, and if none found it adds one to the list
addOrReplace::(CmdInterpreterStatus,[CmdInterpreterStatus])->[CmdInterpreterStatus]
addOrReplace (val,status)
                      = case val of
                                  Env x y -> do
                                               case status of
                                                          [] -> (Env x y):[]
                                                          CmdInitialState:ls -> addOrReplace (val,ls)
                                                          (OutputErr xx):_ -> (OutputErr xx):[]
                                                          (Env _ _):ls -> (Env x y):ls
                                  OutputErr x -> (OutputErr x):[]
                                  CmdInitialState -> status

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

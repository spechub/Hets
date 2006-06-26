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


extractFrom::([CmdInterpreterStatus],CmdInterpreterStatusID) -> Maybe CmdInterpreterStatus
extractFrom (status,cmdID)
                          = case cmdID of
                                        EnvID -> do 
                                                   case status of 
                                                                [] -> Nothing
                                                                (Env x y):_ -> Just (Env x y)
                                                                _:ls-> (extractFrom (ls,cmdID))

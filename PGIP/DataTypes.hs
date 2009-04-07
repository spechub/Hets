{- |
Module      : $Header$
Description : Internal data types of the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.DataTypes describes the internal states(or datatypes) of the CMDL
interface.
-}


module PGIP.DataTypes
       ( CMDL_State(..)
       , CMDL_CmdDescription(..)
       , CMDL_CmdPriority(..)
       , CMDL_CmdFnClasses(..)
       , CMDL_CmdRequirements(..)
       , CMDL_Channel(..)
       , CMDL_ChannelType(..)
       , CMDL_ChannelProperties(..)
       , CMDL_Socket(..)
       , CMDL_UseTranslation(..)
       , CMDL_ProverConsChecker(..)
       , CMDL_PrompterState(..)
       , CMDL_Message(..)
       , CMDL_ListAction(..)
       , CMDL_GoalAxiom(..)
       ) where


import Interfaces.DataTypes

import System.IO
import Network

data CMDL_GoalAxiom =
   ChangeGoals
 | ChangeAxioms



data CMDL_ProverConsChecker =
   Use_prover
 | Use_consChecker

data CMDL_UseTranslation =
   Do_translate
 | Dont_translate

-- * CMDL datatypes

-- | CMDLState contains all information the CMDL interface
-- might use at any time.
data CMDL_State = CMDL_State {
  -- | Interface state (should be common for any interface)
  intState :: IntState,
  -- | promter of the interface
  prompter        :: CMDL_PrompterState,
  -- | open comment
  openComment     :: Bool,
  -- | opened connections
  connections     :: [CMDL_Channel],
  -- | output of interface
  output          :: CMDL_Message
 }

data CMDL_PrompterState = CMDL_PrompterState {
  fileLoaded :: String,
  prompterHead :: String
  }

-- | Description of a command ( in  order to have a uniform access to any of
-- the commands
data CMDL_CmdDescription = CMDL_CmdDescription {
  cmdNames       :: [String],
  cmdDescription :: String,
  cmdInput       :: String,
  cmdPriority    :: CMDL_CmdPriority,
  cmdFn          :: CMDL_CmdFnClasses,
  cmdReq         :: CMDL_CmdRequirements
  }



-- | Some commands have different status, for example 'end-script'
-- needs to be processed even though the interface is in reading script
-- state. The same happens with '}%' even though the interface is in
-- multi line comment state. In order not to treat this few commands
-- separately from the other it is easy just to give to all commands
-- different priorities
data CMDL_CmdPriority =
   CmdNoPriority
 | CmdGreaterThanComments
 | CmdGreaterThanScriptAndComments

-- | Any command belongs to one of the following classes of functions,
-- a) f :: s -> IO s
-- b) f :: String -> s -> IO s
data CMDL_CmdFnClasses =
   CmdNoInput (CMDL_State -> IO CMDL_State)
 | CmdWithInput (String -> CMDL_State -> IO CMDL_State)

-- | Datatype describing the types of commands according
-- to what they expect as input
data CMDL_CmdRequirements =
   ReqNodes
 | ReqEdges
 | ReqNodesAndEdges
 | ReqProvers
 | ReqConsCheck
 | ReqComorphism
 | ReqFile
 | ReqGNodes
 | ReqGEdges
 | ReqGNodesAndGEdges
 | ReqAxm
 | ReqGoal
 | ReqNumber
 | ReqNothing
 | ReqUnknown


-- Communication channel datatypes -----------------------------------------

-- | CMDLSocket takes care of opened sockets for comunication with other
-- application like the Broker in the case of PGIP
data CMDL_Channel = CMDL_Channel {
   chName        :: String,
   chType        :: CMDL_ChannelType,
   chHandler     :: Handle,
   chSocket      :: Maybe CMDL_Socket,
   chProperties  :: CMDL_ChannelProperties
   }


-- | Channel type describes different type of channel
data CMDL_ChannelType =
 -- socket type
   ChSocket
 -- file type
 | ChFile
 -- std in
 | ChStdin
 -- std out
 | ChStdout

-- | Channel properties describes what a channel can do
data CMDL_ChannelProperties =
   ChRead
 | ChWrite
 | ChReadWrite

-- | Describes a socket
data CMDL_Socket = CMDL_Socket {
   socketHandler     :: Socket,
   socketHostName    :: HostName,
   socketPortNumber  :: PortNumber
   }

-- | Datatype describing the list of possible action on a list
-- of selected items
data CMDL_ListAction =
   ActionSet
 | ActionSetAll
 | ActionDel
 | ActionDelAll
 | ActionAdd


-- | output message given by the interface
data CMDL_Message = CMDL_Message {
         outputMsg  :: String,
         warningMsg :: String,
         errorMsg   :: String
         }





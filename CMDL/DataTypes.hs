{- |
Module      : $Header$
Description : Internal data types of the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.DataTypes describes the internal states(or datatypes) of the CMDL
interface.
-}


module CMDL.DataTypes
  ( CmdlState (..)
  , emptyCmdlState
  , CmdlCmdDescription (..)
  , cmdInput
  , cmdName
  , CmdlCmdPriority (..)
  , CmdlCmdFnClasses (..)
  , CmdlCmdRequirements (..)
  , CmdlChannel (..)
  , CmdlChannelType (..)
  , CmdlChannelProperties (..)
  , CmdlSocket (..)
  , CmdlUseTranslation (..)
  , CmdlProverConsChecker (..)
  , CmdlPrompterState (..)
  , CmdlMessage (..)
  , emptyCmdlMessage
  , CmdlListAction (..)
  , CmdlGoalAxiom (..)
  ) where

import Interfaces.DataTypes
import Interfaces.Command

import Driver.Options

import Network

import System.IO (Handle)

data CmdlGoalAxiom =
    ChangeGoals
  | ChangeAxioms

data CmdlProverConsChecker =
    Use_prover
  | Use_consChecker

data CmdlUseTranslation =
    Do_translate
  | Dont_translate

-- * CMDL datatypes

-- | CMDLState contains all information the CMDL interface
-- might use at any time.
data CmdlState = CmdlState
  { intState :: IntState -- ^ common interface state
  , prompter :: CmdlPrompterState -- ^ promter of the interface
  , openComment :: Bool -- ^ open comment
  , connections :: [CmdlChannel] -- ^ opened connections
  , output :: CmdlMessage -- ^ output of interface
  , hetsOpts :: HetcatsOpts  -- ^ hets command options
  }

-- | Creates an empty CmdlState
emptyCmdlState :: HetcatsOpts -> CmdlState
emptyCmdlState opts = CmdlState
  { intState = IntState
      { i_state = Nothing
      , i_hist = IntHistory
          { undoList = []
          , redoList = [] }
      , filename = [] }
  , prompter = CmdlPrompterState
      { fileLoaded = ""
      , prompterHead = "> " }
  , output = emptyCmdlMessage
  , openComment = False
  , connections = []
  , hetsOpts = opts }

data CmdlPrompterState = CmdlPrompterState
  { fileLoaded :: String
  , prompterHead :: String }

-- | Description of a command ( in  order to have a uniform access to any of
-- the commands
data CmdlCmdDescription = CmdlCmdDescription
  { cmdDescription :: Command
  , cmdPriority :: CmdlCmdPriority
  , cmdFn :: CmdlCmdFnClasses
  , cmdReq :: CmdlCmdRequirements }

cmdInput :: CmdlCmdDescription -> String
cmdInput = cmdInputStr . cmdDescription

cmdName :: CmdlCmdDescription -> String
cmdName = cmdNameStr . cmdDescription

-- | Some commands have different status, for example 'end-script'
-- needs to be processed even though the interface is in reading script
-- state. The same happens with '}%' even though the interface is in
-- multi line comment state. In order not to treat this few commands
-- separately from the other it is easy just to give to all commands
-- different priorities
data CmdlCmdPriority =
    CmdNoPriority
  | CmdGreaterThanComments
  | CmdGreaterThanScriptAndComments

-- | Any command belongs to one of the following classes of functions,
-- a) f :: s -> IO s
-- b) f :: String -> s -> IO s
data CmdlCmdFnClasses =
    CmdNoInput (CmdlState -> IO CmdlState)
  | CmdWithInput (String -> CmdlState -> IO CmdlState)

-- | Datatype describing the types of commands according
-- to what they expect as input
data CmdlCmdRequirements =
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
data CmdlChannel = CmdlChannel
  { chName :: String
  , chType :: CmdlChannelType
  , chHandler :: Handle
  , chSocket :: Maybe CmdlSocket
  , chProperties  :: CmdlChannelProperties }

-- | Channel type describes different type of channel
data CmdlChannelType =
    ChSocket
  | ChFile
  | ChStdin
  | ChStdout

-- | Channel properties describes what a channel can do
data CmdlChannelProperties =
    ChRead
  | ChWrite
  | ChReadWrite

-- | Describes a socket
data CmdlSocket = CmdlSocket
  { socketHandler :: Socket
  , socketHostName :: HostName
  , socketPortNumber :: PortNumber }

-- | Datatype describing the list of possible action on a list
-- of selected items
data CmdlListAction =
    ActionSet
  | ActionSetAll
  | ActionDel
  | ActionDelAll
  | ActionAdd

-- | output message given by the interface
data CmdlMessage = CmdlMessage
  { outputMsg :: String
  , warningMsg :: String
  , errorMsg :: String }

emptyCmdlMessage :: CmdlMessage
emptyCmdlMessage = CmdlMessage
  { errorMsg = []
  , outputMsg = []
  , warningMsg = [] }

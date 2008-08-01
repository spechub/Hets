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
       , CMDL_History(..)
       , CMDL_UndoRedoElem(..)
       , CMDL_ListChange(..)
       , CMDL_CmdDescription(..)
       , CMDL_CmdHistoryDescription(..)
       , CMDL_CmdPriority(..)
       , CMDL_CmdFnClasses(..)
       , CMDL_CmdType(..)
       , CMDL_CmdRequirements(..)
       , CMDL_DevGraphState(..)
       , CMDL_ProveState(..)
       , CMDL_ProofAbstractState(..)
       , CMDL_ListAction(..)
       , CMDL_GoalAxiom(..)
       , CMDL_Output(..)
       , CMDL_Channel(..)
       , CMDL_ChannelType(..)
       , CMDL_ChannelProperties(..)
       , CMDL_Socket(..)
       , CMDL_UseTranslation(..)
       , CMDL_ProverConsChecker(..)
       , CMDL_PrompterState(..)
       ) where

import Static.DevGraph
import Logic.Comorphism
import Logic.Logic
import System.IO
import Network
import Syntax.AS_Library
import Proofs.AbstractState


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
  -- | development  graph mode information
  devGraphState   :: Maybe CMDL_DevGraphState,
  -- | prove mode information
  proveState      :: Maybe CMDL_ProveState,
  -- | promter of the interface
  prompter        :: CMDL_PrompterState,
  -- | output of the last command
  output          :: CMDL_Output,
  -- | history
  history         :: CMDL_History,
  -- | open comment
  openComment     :: Bool,
 -- | opened connections
  connections     :: [CMDL_Channel]
 }

data CMDL_PrompterState = CMDL_PrompterState {
  fileLoaded :: String,
  selectedNodes :: String,
  selectedTranslations :: String,
  prompterHead :: String
  }
-- History datatypes -------------------------------------------------------

-- | Description of the internal history of the CMDL interface
data CMDL_History = CMDL_History {
  -- | history for undo command
  undoList :: [CMDL_CmdHistoryDescription],
  -- | history for redo command
  redoList :: [CMDL_CmdHistoryDescription],
  -- | for undo function history
  oldEnv          :: Maybe LibEnv,
  -- | History elements
  undoInstances  :: [([CMDL_UndoRedoElem], [CMDL_UndoRedoElem])],
  redoInstances  :: [([CMDL_UndoRedoElem], [CMDL_UndoRedoElem])]
  }

-- | History element for the proof state, describes the value that is being
-- change
data CMDL_UndoRedoElem =
   UseThmChange Bool
 | Save2FileChange Bool
 | ProverChange (Maybe G_prover)
 | ConsCheckerChange (Maybe G_cons_checker)
 | ScriptChange String
 | LoadScriptChange Bool
 | CComorphismChange (Maybe AnyComorphism)
 | ListChange [CMDL_ListChange]
 | ProveChange LibEnv [CMDL_ListChange]

data CMDL_ListChange =
   AxiomsChange [String] Int
 | GoalsChange [String] Int


-- Command description datatypes -------------------------------------------

-- | Description of a command ( in  order to have a uniform access to any of
-- the commands
data CMDL_CmdDescription = CMDL_CmdDescription {
--  cmdType        :: CMDL_CmdType,
--  cmdNames       :: [String],
--  cmdInput       :: String,
  cmdInfo        :: CMDL_CmdHistoryDescription,
  cmdDescription :: String,
  cmdPriority    :: CMDL_CmdPriority,
  cmdFn          :: CMDL_CmdFnClasses,
  cmdReq         :: CMDL_CmdRequirements
  }


data CMDL_CmdHistoryDescription = CMDL_CmdHistoryDescription {
  cmdType        :: CMDL_CmdType,
  cmdNames       :: [String],
  cmdInput       :: String
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

-- | Types of different commands available (DG command, Prove command,
-- Info command or System command)
data CMDL_CmdType =
   DgCmd
 | ProveCmd
 | InfoCmd
 | SelectCmd
 | SelectCmdAll
 | SystemCmd
 | EvalCmd
 | UndoRedoCmd


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


-- Development Graph state datatypes ---------------------------------------

-- | During the development graph mode, the CMDL interface
-- will use the information stored in CMDLDevGraphState which
-- consist of the library loaded and a list of all nodes
-- and edges.
data CMDL_DevGraphState = CMDL_DevGraphState {
    ln               :: LIB_NAME,
    libEnv           :: LibEnv
    }

-- Prove state datatypes ---------------------------------------------------

-- | During the prove mode, the CMDL interface will use the
-- informations stored in the Prove state, which consists of
-- the list of elements selected,  the list of comorphism
-- applied to the list (where the first in the list is the
-- last applied comorphism, the selected prover and the
-- script.
data CMDL_ProveState =
  CMDL_ProveState {
    -- | selected nodes as elements (only the theory and the
    -- node number from where the theory was taken)
    elements     :: [CMDL_ProofAbstractState] ,
    -- | composed comorphism resulting from all the selected
    -- comorphisms.
    cComorphism :: Maybe AnyComorphism,
    -- | Selected prover
    prover      :: Maybe G_prover,
    -- | Selected consistency checker
    consChecker :: Maybe G_cons_checker,
    -- | Save for each goal the output from the prover in a file
    save2file   :: Bool,
    -- | Use proven theorems in subsequent proofs
    useTheorems :: Bool,
    -- | Script to be used when proving
    script      :: String,
    -- | If script is currently being inserted
    loadScript  :: Bool
   }


-- AbstractState depends on lid and sentence, and in order
-- not to change to much CMDLProveState requires some
-- independent type
-- also CMDL interface requires to keep track of the node
-- number
data CMDL_ProofAbstractState = forall lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1 .
         Logic lid1 sublogics1 basic_spec1 sentence1
         symb_items1 symb_map_items1 sign1 morphism1
         symbol1 raw_symbol1 proof_tree1 =>
     Element (ProofState lid1 sentence1) Int

-- | Datatype describing the list of possible action on a list
-- of selected items
data CMDL_ListAction =
   ActionSet
 | ActionSetAll
 | ActionDel
 | ActionDelAll
 | ActionAdd

data CMDL_GoalAxiom =
   ChangeGoals
 | ChangeAxioms


-- Communication channel datatypes -----------------------------------------

data CMDL_Output = CMDL_Output {
  -- | error String, any error occurance has to fill
  -- this String with an error message
  errorMsg        :: String,
  -- | any function that needs to print something on the
  -- screen should use this outputMsg to store the output
  outputMsg       :: String,
  fatalError      :: Bool
   }

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




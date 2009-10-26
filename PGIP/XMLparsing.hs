{- |
Module      : $Header$
Description : XML processing for the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.XMLparsing contains commands for parsing or creating XML messages
-}

module PGIP.XMLparsing where

import PGIP.XMLstate

import CMDL.DataTypes
import CMDL.DataTypesUtils
import CMDL.DgCommands (cUse)
import CMDL.ProcessScript
import CMDL.Interface (cmdlRunShell)

import Interfaces.DataTypes
import Interfaces.Command
import Interfaces.Utils (emptyIntIState)

import Driver.Options
import Driver.ReadFn

import qualified Static.ToXml as ToXml
import Static.DevGraph

import Common.LibName
import Common.ToXml

import Text.XML.Light as XML

import Network (connectTo, PortID(PortNumber), accept, listenOn)

import System.IO

import Data.List (isInfixOf)

-- | Generates the XML packet that contains information about what
-- commands can the interface respond to
addPGIPHandshake :: CmdlPgipState -> CmdlPgipState
addPGIPHandshake pgipData = let
       el_askpgip        = genPgipElem "askpgip"
       el_askpgml        = genPgipElem "askpgml"
       el_askprefs       = genPgipElem "askprefs"
       el_getprefs       = genPgipElem "getprefs"
       el_setprefs       = genPgipElem "setprefs"
       el_proverinit     = genPgipElem "proverinit"
       el_proverexit     = genPgipElem "proverexit"
       el_startquiet     = genPgipElem "startquiet"
       el_stopquiet      = genPgipElem "stopquiet"
       el_pgmlsymbolon   = genPgipElem "pgmlsymbolon"
       el_pgmlsymboloff  = genPgipElem "pgmlsymboloff"
       el_dostep         = genPgipElem "dostep"
       el_undostep       = genPgipElem "undostep"
       el_redostep       = genPgipElem "redostep"
       el_abortgoal      = genPgipElem "abortgoal"
       el_forget         = genPgipElem "forget"
       el_restoregoal    = genPgipElem "restoregoal"
       el_askids         = genPgipElem "askids"
       el_showid         = genPgipElem "showid"
       el_askguise       = genPgipElem "askguise"
       el_parsescript    = genPgipElem "parsescript"
       el_showproofstate = genPgipElem "showproofstate"
       el_showctxt       = genPgipElem "showctxt"
       el_searchtheorems = genPgipElem "searchtheorems"
       el_setlinewidth   = genPgipElem "setlinewidth"
       el_viewdoc        = genPgipElem "viewdoc"
       el_doitem         = genPgipElem "doitem"
       el_undoitem       = genPgipElem "undoitem"
       el_redoitem       = genPgipElem "redoitem"
       el_aborttheory    = genPgipElem "aborttheory"
       el_retracttheory  = genPgipElem "retracttheory"
       el_loadfile       = genPgipElem "loadfile"
       el_openfile       = genPgipElem "openfile"
       el_closefile      = genPgipElem "closefile"
       el_abortfile      = genPgipElem "abortfile"
       el_changecwd      = genPgipElem "changecwd"
       el_systemcmd      = genPgipElem "systemcmd"
       pgip_elems =
             [ el_askpgip
             , el_askpgml
             , el_askprefs
             , el_getprefs
             , el_setprefs
             , el_proverinit
             , el_proverexit
             , el_startquiet
             , el_stopquiet
             , el_pgmlsymbolon
             , el_pgmlsymboloff
             , el_dostep
             , el_undostep
             , el_redostep
             , el_abortgoal
             , el_forget
             , el_restoregoal
             , el_askids
             , el_showid
             , el_askguise
             , el_parsescript
             , el_showproofstate
             , el_showctxt
             , el_searchtheorems
             , el_setlinewidth
             , el_viewdoc
             , el_doitem
             , el_undoitem
             , el_redoitem
             , el_aborttheory
             , el_retracttheory
             , el_loadfile
             , el_openfile
             , el_closefile
             , el_abortfile
             , el_changecwd
             , el_systemcmd
             ]
   in if useXML pgipData
       then addPGIPElement pgipData
            $ add_attr (mkAttr "version" "2.0")
            $ unode "acceptedpgipelems" pgip_elems
       else pgipData

-- | The function executes a communication step, i.e. waits for input,
-- processes the message and outputs the answer
communicationStep :: CmdlPgipState -> CmdlState -> IO (CmdlPgipState, CmdlState)
communicationStep pgD st = do
   -- tries to read a packet from the input
  b <- hIsEOF (hin pgD)
  if b then return (pgD { stop = True }, st) else do
   tmp <- timeoutReadPacket (maxWaitTime pgD) pgD
   case tmp of
    Nothing -> if resendMsgIfTimeout pgD
      -- if the interface receives nothing in the given timeframe
      -- described by maxWaitTime and the flag resendMsgIfTimeout is
      -- set, that the interface resends last packet assuming that last
      -- send was a fail
                then do
                       nwpgD <- sendPGIPData (hetsOpts st) pgD
                       communicationStep nwpgD st
       -- if the flag is not set, that the network waits some more for the
       -- broker to respond or give a new command
                else communicationStep pgD st
    -- if something is received, that the commands are parsed and executed
    -- and a response is generated
    Just smtxt ->
      do
        let cmds = parseMsg pgD smtxt
            refseqNb = getRefseqNb smtxt
        (nwSt, nwPgD) <- processCmds cmds st $ resetPGIPData $
                           pgD { refSeqNb = refseqNb }
        if useXML pgD then do
                 nwPgipSt <- sendPGIPData (hetsOpts nwSt) nwPgD
                 return (nwPgipSt, nwSt)
          else do
                 nwPgD' <- sendMSGData (hetsOpts nwSt) nwPgD
                 return (nwPgD', nwSt)

-- | Comunicate over a port
cmdlListenOrConnect2Port :: HetcatsOpts -> CmdlState -> IO CmdlState
cmdlListenOrConnect2Port opts state = do
    let portNb = listen opts
        conPN = connectP opts
        hostName = connectH opts
        swXML = xmlFlag opts
    servH <- if portNb /= -1 then do
        putIfVerbose opts 1 $ "Starting hets. Listen to port " ++ show portNb
        servSock <- listenOn $ PortNumber $ fromIntegral portNb
        (servH, _, _) <- accept servSock
        return servH
      else if conPN /= -1 then do
        putIfVerbose opts 1 $ "Starting hets. Connecting to port "
          ++ show conPN ++ " on host " ++ hostName
        connectTo hostName $ PortNumber $ fromIntegral conPN
      else error "cmdlListenOrConnect2Port: missing port number"
    cmdlStartLoop swXML servH servH 1000 state

-- | Reads from a handle, it waits only for a certain amount of time,
-- if no input comes it will return Nothing
timeoutReadPacket :: Int -> CmdlPgipState -> IO (Maybe String)
timeoutReadPacket untilTimeout st = do
    let h = hin st
    smtmp <- hWaitForInput h untilTimeout
    if smtmp then do
            ms <- if useXML st
                    then readPacket [] h
                    else hGetLine h
            return $ Just ms
      else return Nothing

-- | Waits until it reads an entire XML packet
readPacket :: String -> Handle -> IO String
readPacket acc hf = do
    tmp <- hGetLine hf
    let str = acc ++ tmp ++ "\n"
    if isInfixOf "</pgip>" tmp
      then return str
      else readPacket str hf

cmdlStartLoop :: Bool -> Handle -> Handle -> Int -> CmdlState
              -> IO CmdlState
cmdlStartLoop swXML h_in h_out timeOut state = do
    pgData <- genCMDLPgipState  swXML h_in h_out timeOut
    let pgD = addPGIPReady $ addPGIPHandshake $ resetPGIPData pgData
    pgD' <- sendPGIPData (hetsOpts state) pgD
    waitLoop pgD' state

waitLoop :: CmdlPgipState -> CmdlState -> IO CmdlState
waitLoop pgData state = do
  (pgData', state') <- communicationStep pgData state
  if stop pgData'
    then return state'
    else waitLoop pgData' state'

-- | Runs a shell in which the communication is expected to be
-- through XML packets
cmdlRunXMLShell :: CmdlState -> IO CmdlState
cmdlRunXMLShell = cmdlStartLoop True stdin stdout (-1)

-- | Processes a list of input files
processInput :: HetcatsOpts -> [FilePath] -> CmdlState -> IO CmdlState
processInput opts ls state = case ls of
    []   -> return state
    l : ll -> (case guess l GuessIn of
               ProofCommand -> cmdlProcessScriptFile
               _ -> cUse) l state >>= processInput opts ll

cmdlRun :: HetcatsOpts -> IO CmdlState
cmdlRun opts =
  processInput opts (infiles opts) (emptyCmdlState opts) >>=
  if isRemote opts
    then cmdlListenOrConnect2Port opts
    else if interactive opts
           then if xmlFlag opts
                  then cmdlRunXMLShell
                  else cmdlRunShell
           else return

processString :: [CmdlXMLcommands] -> String -> CmdlState -> CmdlPgipState
  -> IO (CmdlState, CmdlPgipState)
processString pl str st pgSt = do
  (nwSt, mCmd) <- cmdlProcessString "" 0 str st
  postProcessCmd pl nwSt pgSt mCmd

-- copy messages to pgip state
processMsgs :: CmdlState -> CmdlPgipState -> (CmdlPgipState, String)
processMsgs nwSt pgSt =
  let o = output nwSt
      ms = outputMsg o
      ws = warningMsg o
      es = errorMsg o
      -- there should be at most one
  in (if null es then addPGIPAnswer ms ws pgSt else addPGIPError es pgSt, es)

processCommand :: [CmdlXMLcommands] -> Command -> CmdlState -> CmdlPgipState
  -> IO (CmdlState, CmdlPgipState)
processCommand pl cmd st pgSt = do
  nwSt <- cmdlProcessCmd cmd st
  postProcessCmd pl nwSt pgSt (Just cmd)

-- postprocess a previously run command and recurse
postProcessCmd :: [CmdlXMLcommands] -> CmdlState -> CmdlPgipState
  -> Maybe Command -> IO (CmdlState, CmdlPgipState)
postProcessCmd pl nwSt0 pgSt mCmd = let
  (pgSt1, es) = processMsgs nwSt0 pgSt
  nwSt = nwSt0 { output = emptyCmdlMessage } -- remove messages form cmdl state
  in if null es then processCmds pl nwSt $ informCmd nwSt mCmd pgSt1 else
  return (nwSt, addPGIPReady pgSt1)

informCmd :: CmdlState -> Maybe Command -> CmdlPgipState -> CmdlPgipState
informCmd nwSt mCmd pgSt1 = case (getMaybeLib $ intState nwSt, mCmd) of
          (Just (lN, lEnv), Just cmd) -> case cmd of
            SelectCmd LibFile _ ->
              informDGraph lN lEnv $ addPGIPElement pgSt1
                $ add_attr (mkAttr "url" $ libNameToFile lN)
                $ unode "informfileloaded" ()
            GlobCmd g | g < ProveCurrent ->
              informDGraph lN lEnv pgSt1
            _ -> pgSt1
          _ -> pgSt1

informDGraph :: LibName -> LibEnv -> CmdlPgipState -> CmdlPgipState
informDGraph lN lEnv pgSt =
  addPGIPElement pgSt $ unode "informdevelopmentgraph" $ ToXml.dGraph lEnv
    $ lookupDGraph lN lEnv

-- | Executes given commands and returns output message and the new state
processCmds :: [CmdlXMLcommands] -> CmdlState -> CmdlPgipState
  -> IO (CmdlState, CmdlPgipState)
processCmds cmds state pgipSt = do
    let opts = hetsOpts state
    case cmds of
     [] -> return (state, addPGIPReady pgipSt)
            -- ensures that the response is ended with a ready element
            -- such that the broker does wait for more input
     XmlExecute str : l -> processString l str state (resetPGIPData pgipSt)
     XmlExit : l -> processCmds l state $
         addPGIPAnswer "Exiting prover" [] pgipSt { stop = True }
     XmlAskpgip : l -> processCmds l state $ addPGIPHandshake pgipSt
     XmlProverInit : l -> processCmds l (emptyCmdlState opts) $
         addPGIPAnswer "Prover state was reset" [] pgipSt
     XmlStartQuiet : l -> do
         -- To inform that quiet mode is enabled we need to send this with the
         -- old options.
         let pgD = addPGIPReady $ addPGIPAnswer "Quiet mode enabled" [] pgipSt
         pgipSt' <- if useXML pgD
                      then sendPGIPData opts pgD
                      else sendMSGData opts pgD
         processCmds l (state { hetsOpts = opts { verbose = 0 } }) pgipSt'
     XmlStopQuiet : l ->
                  processCmds l (state { hetsOpts = opts { verbose = 1 } }) $
                    addPGIPAnswer "Quiet mode disabled" [] pgipSt
     XmlOpenGoal str : l -> processCommand l (SelectCmd Goal str) state pgipSt
     XmlCloseGoal str : l -> processCommand (XmlGiveUpGoal str : l)
         (GlobCmd ProveCurrent) state pgipSt
     XmlGiveUpGoal str : l -> processString l ("del goals " ++ str) state pgipSt
     XmlUnknown str : l -> processCmds l state $
           addPGIPAnswer [] ("Unknown command: " ++ str) pgipSt
     XmlUndo : l -> processCommand l (GlobCmd UndoCmd) state pgipSt
     XmlRedo : l -> processCommand l (GlobCmd RedoCmd) state pgipSt
     XmlForget str : l -> processString l ("del axioms " ++ str) state pgipSt
     XmlOpenTheory str : l -> processString l str state pgipSt
     XmlCloseTheory _ : l -> let
         nwSt = case i_state $ intState state of
           Nothing -> state
           Just ist -> add2hist [IStateChange $ Just ist] $ state
             { intState = (intState state)
                 { i_state = Just $ emptyIntIState (i_libEnv ist)
                     $ i_ln ist }}
         in processCmds l nwSt $ addPGIPAnswer "Theory closed" [] pgipSt
     XmlCloseFile _ : l -> processCmds l (emptyCmdlState opts)
                   (addPGIPAnswer "File closed" [] pgipSt)
     XmlParseScript str : _ ->
         processCmds [] state . addPGIPElement pgipSt $ addPGIPMarkup str
     XmlLoadFile str : l ->
         processCommand l (SelectCmd LibFile str) state pgipSt

{- deleting axioms or goals should be implemented via a select command after
inspecting the current axioms or goals. The current strings do not work. -}

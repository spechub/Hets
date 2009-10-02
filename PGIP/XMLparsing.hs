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
import PGIP.ParseProofScript as Parser

import CMDL.DataTypes
import CMDL.DataTypesUtils

import Interfaces.DataTypes
import Interfaces.Command
import Interfaces.Utils(emptyIntIState)

import Driver.Options
import Driver.ReadFn

import qualified Static.ToXml as ToXml
import Static.DevGraph

import Common.LibName
import Common.ToXml
import Common.Utils

import Text.XML.Light as XML

import Network (connectTo, PortID(PortNumber), accept, listenOn)

import System.IO

import Data.List (isInfixOf)
import Control.Monad

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
communicationStep:: CmdlPgipState -> CmdlState ->
                     IO (CmdlPgipState, CmdlState)
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
                       nwpgD <- sendPGIPData pgD
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
                 nwPgipSt <- sendPGIPData nwPgD
                 return (nwPgipSt, nwSt)
          else do
                 nwPgD' <- sendMSGData nwPgD
                 return (nwPgD', nwSt)

-- | Comunicate over a port
cmdlListenOrConnect2Port :: HetcatsOpts -> IO CmdlState
cmdlListenOrConnect2Port opts = do
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
    cmdlStartLoop opts swXML servH servH 1000

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

cmdlStartLoop :: HetcatsOpts -> Bool -> Handle -> Handle -> Int -> IO CmdlState
cmdlStartLoop opts swXML h_in h_out timeOut = do
    pgData <- genCMDLPgipState  swXML h_in h_out timeOut
    let pgD = addPGIPReady $ addPGIPHandshake $ resetPGIPData pgData
    pgD' <- sendPGIPData pgD
    waitLoop pgD' $ emptyCmdlState opts

waitLoop :: CmdlPgipState -> CmdlState -> IO CmdlState
waitLoop pgData state = do
  (pgData', state') <- communicationStep pgData state
  if stop pgData'
    then return state'
    else waitLoop pgData' state'

-- | Runs a shell in which the communication is expected to be
-- through XML packets
cmdlRunXMLShell :: HetcatsOpts -> IO CmdlState
cmdlRunXMLShell opts = cmdlStartLoop opts True stdin stdout (-1)

process :: [CmdlXMLcommands] -> String -> CmdlState -> CmdlPgipState
        -> IO (CmdlState, CmdlPgipState)
process pl str st pgSt = do
  (nwSt, mCmd) <- cmdlProcessString "" 0 str st
  let o = output nwSt
      ms = outputMsg o
      ws = warningMsg o
      es = errorMsg o
      -- there should be at most one
      pgSt1 = if null es then addPGIPAnswer ms ws pgSt
              else addPGIPError es pgSt
  if null es then
    let pgSt2 = case (getMaybeLib $ intState nwSt, mCmd) of
          (Just (lN, lEnv), Just cmd) -> case cmd of
            SelectCmd LibFile _ ->
              informDGraph lN lEnv $ addPGIPElement pgSt1
                $ add_attr (mkAttr "url" $ libNameToFile (hetsOpts nwSt) lN)
                $ unode "informfileloaded" ()
            GlobCmd g | g < ProveCurrent ->
              informDGraph lN lEnv pgSt1
            _ -> pgSt1
          _ -> pgSt1
    in processCmds pl nwSt pgSt2
    else return (nwSt, addPGIPReady pgSt1)

informDGraph :: LibName -> LibEnv -> CmdlPgipState -> CmdlPgipState
informDGraph lN lEnv pgSt =
  addPGIPElement pgSt $ unode "informdevelopmentgraph" $ ToXml.dGraph lEnv
    $ lookupDGraph lN lEnv

cmdlProcessString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
cmdlProcessString fp l ps st = case parseSingleLine fp l ps of
  Left err -> return (genErrorMsg err st, Nothing)
  Right c -> let
      cm = Parser.command c
      cmd = cmdDescription cm
      addCmd = fmap $ \ nst -> (nst, Just cmd)
    in case cmdFn cm of
    CmdNoInput f -> addCmd $ f st
    CmdWithInput f -> addCmd $ f (cmdInputStr cmd) st

cmdlProcessScriptFile :: FilePath -> CmdlState -> IO CmdlState
cmdlProcessScriptFile fp st = do
  str <- readFile fp
  foldM (\ nst (s, n) -> do
      (cst, _) <- cmdlProcessString fp n s nst
      let o = output cst
          ms = outputMsg o
          ws = warningMsg o
          es = errorMsg o
      unless (null ms) $ putStrLn ms
      unless (null ws) $ putStrLn $ "Warning:\n" ++ ws
      unless (null es) $ putStrLn $ "Error:\n" ++ es
      return cst { output = emptyCmdlMessage }) st
    $ number $ lines str

-- | Executes given commands and returns output message and the new state
processCmds :: [CmdlXMLcommands] -> CmdlState -> CmdlPgipState
            -> IO (CmdlState, CmdlPgipState)
processCmds cmds state pgipSt = do
    let opts = hetsOpts state
    case cmds of
     [] -> return (state, addPGIPReady pgipSt)
            -- ensures that the response is ended with a ready element
            -- such that the broker does wait for more input
     XmlExecute str : l -> process l str state (resetPGIPData pgipSt)
     XmlExit : l -> processCmds l state $
         addPGIPAnswer "Exiting prover" [] pgipSt { stop = True }
     XmlAskpgip : l -> processCmds l state $ addPGIPHandshake pgipSt
     XmlProverInit : l -> processCmds l (emptyCmdlState opts) $
         addPGIPAnswer "Prover state was reset" [] pgipSt
     XmlStartQuiet : l ->
                  -- Quiet not yet implemented !!
                  processCmds l state $ addPGIPAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = True }
     XmlStopQuiet : l ->
                  -- Quiet not yet implemented !!
                  -- use proper tmp-files and avoid duplicate code!
                  processCmds l state $ addPGIPAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = False }
     XmlOpenGoal str : l -> process l ("set goals " ++ str) state pgipSt
     XmlCloseGoal str : l ->
         processCmds (XmlGiveUpGoal str : XmlExecute "prove" : l) state pgipSt
     XmlGiveUpGoal str : l ->
       process l ("del goals " ++ str) state pgipSt
     XmlUnknown str : l -> processCmds l state $
           addPGIPAnswer [] ("Unknown command: " ++ str) pgipSt
     XmlUndo : l -> process l "undo" state pgipSt
     XmlRedo : l -> process l "redo" state pgipSt
     XmlForget str : l -> process l ("del axioms " ++ str) state pgipSt
     XmlOpenTheory str : l -> process l str state pgipSt
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
     XmlLoadFile str : l -> process l ("use " ++ str) state pgipSt

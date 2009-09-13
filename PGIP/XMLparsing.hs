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

module PGIP.XMLparsing
where

import Network(connectTo, PortID(PortNumber), accept, listenOn)
import System.IO
import Data.List(isInfixOf)

import PGIP.MarkPgip(genQName, addPgipMarkUp)
import PGIP.XMLstate
import CMDL.Interface(cmdlProcessString, emptyCMDL_State)
import CMDL.DataTypes(CMDL_Message(..), CMDL_State(output, intState))
import CMDL.DataTypesUtils(add2hist)
import Interfaces.DataTypes
import Interfaces.Utils(emptyIntIState)
import Text.XML.Light as XML

-- | Generates the XML packet that contains information about what
-- commands can the interface respond to
genHandShake :: CMDL_PgipState -> CMDL_PgipState
genHandShake pgipData
 = let el_askpgip        = genPgipElem "askpgip"
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
       xmlrootElem = Elem $ blank_element {
         elName = genQName "usespgip",
         elAttribs = [Attr { attrKey = genQName "version",
                                       attrVal = "2.0" } ],
         elContent = [
            Elem XML.Element {
                    elName    = genQName "acceptedpgipelems",
                    elAttribs = [],
                    elContent = pgip_elems,
                    elLine    = Nothing } ],
         elLine = Nothing }
   in if useXML pgipData
       then addToContent pgipData xmlrootElem
       else pgipData

-- | The function executes a communication step, i.e. waits for input,
-- processes the message and outputs the answer
communicationStep:: CMDL_PgipState -> CMDL_State ->
                     IO (CMDL_PgipState, CMDL_State)
communicationStep pgD st =
  do
   -- tries to read a packet from the input
   tmp <- timeoutReadPacket (maxWaitTime pgD) pgD
   case tmp of
    Nothing -> if resendMsgIfTimeout pgD
      -- if the interface receives nothing in the given timeframe
      -- described by maxWaitTime and the flag resendMsgIfTimeout is
      -- set, that the interface resends last packet assuming that last
      -- send was a fail
                then do
                       let nwpgD = addToMsg (showContent $ xmlContent pgD)
                                     [] pgD { seqNb = seqNb pgD + 1 }
                       appendFile "/tmp/razvan.txt" ("Output : "++
                                    theMsg nwpgD ++ "\n")
                       hPutStrLn (hout nwpgD) $ theMsg nwpgD
                       hFlush $ hout nwpgD
                       communicationStep nwpgD st
       -- if the flag is not set, that the network waits some more for the
       -- broker to respond or give a new command
                else communicationStep pgD st
    -- if something is received, that the commands are parsed and executed
    -- and a response is generated
    Just smtxt ->
      do
        cmds <- parseMsg pgD smtxt
        let refseqNb = getRefseqNb smtxt
        (nwSt, nwPgD) <-processCmds cmds st $ resetMsg [] $ pgD {
                                              refSeqNb = refseqNb }
        if useXML pgD
          then do
                 let nwPgipSt = addToMsg (showContent $ xmlContent nwPgD)
                                []  nwPgD { seqNb = seqNb nwPgD + 1 }
                 hPutStrLn (hout pgD) $ theMsg nwPgipSt
                 hFlush $ hout pgD
                 -- this lines take care for each response to have
                 -- a corresponding id and sequence number
                 let refNb = case refseqNb of
                               Just rNb -> " refseq=\""++rNb++"\" "
                               Nothing -> " "
                     mSg = "<pgip tag=\"Hets\" class=\"pg\" id=\"" ++
                           pgip_id pgD ++ "\"" ++ refNb ++ " seq=\"" ++
                           show (seqNb pgD + 1)++"\"><ready /></pgip>"
                 hPutStrLn (hout pgD) mSg
                 hFlush $ hout pgD
                 return (nwPgipSt { seqNb = seqNb nwPgipSt + 1}, nwSt)
          else do
                 hPutStrLn (hout pgD) $ theMsg nwPgD
                 hFlush $ hout pgD
                 return (nwPgD, nwSt)


-- | Comunicates over a port at which the prover should listen
cmdlListen2Port :: Bool -> Int -> IO CMDL_State
cmdlListen2Port swXML portNb
 = do
    putStrLn $ "Starting hets. Listen to port " ++ show portNb
    servSock <- listenOn $ PortNumber (fromIntegral portNb)
    (servH,_,_) <- accept servSock
    pgData <- genCMDLPgipState swXML servH servH 1000
    let pgD = if swXML
               then addReadyXml $ genHandShake $ resetMsg [] pgData
               else resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
      do
       (nwpgD,nwSt) <- communicationStep pgipD st
       if stop nwpgD
         then return nwSt
         else waitLoop nwpgD nwSt

-- | Comunicates over a port to which the prover has to connect
cmdlConnect2Port :: Bool -> String -> Int -> IO CMDL_State
cmdlConnect2Port swXML hostName portNb
 = do
    putStrLn $ "Starting hets. Connecting to port " ++ show portNb
    sockH <- connectTo hostName $ PortNumber (fromIntegral portNb)
    pgData <- genCMDLPgipState swXML sockH sockH 1000
    let pgD = if swXML
               then addReadyXml $ genHandShake $ resetMsg [] pgData
               else resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
      do
       (nwpgD,nwSt) <- communicationStep pgipD st
       if stop nwpgD
         then return nwSt
         else waitLoop nwpgD nwSt

-- | Reads from a handle, it waits only for a certain amount of time,
-- if no input comes it will return Nothing
timeoutReadPacket :: Int -> CMDL_PgipState -> IO (Maybe String)
timeoutReadPacket untilTimeout st
 = do
    smtmp <- hWaitForInput (hin st) untilTimeout
    if smtmp
     then do
            ms <- if useXML st
                    then readPacket [] $ hin st
                    else hGetLine $ hin st
            return $ Just ms
     else return Nothing

-- | Waits until it reads an entire XML packet
readPacket :: String -> Handle -> IO String
readPacket acc hf
 = do
    tmp <- hGetLine hf
    if isInfixOf "</pgip>" tmp
      then return (acc++tmp++"\n")
      else readPacket (acc++tmp++"\n") hf

-- | Runs a shell in which the communication is expected to be
-- through XML packets
cmdlRunXMLShell :: IO CMDL_State
cmdlRunXMLShell
 = do
    pgData <- genCMDLPgipState True stdin stdout (-1)
    let pgD = addReadyXml $ genHandShake $ resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
       do
        (nwpgD,nwSt) <- communicationStep pgipD st
        if stop nwpgD
          then return nwSt
          else waitLoop nwpgD nwSt

-- | It inserts a given string into the XML packet as
-- normal output
genAnswer :: String -> String -> CMDL_PgipState -> CMDL_PgipState
genAnswer msgtxt errmsg st
 = if useXML st
     then
      case errmsg of
       [] -> addToContent st $ genNormalResponse msgtxt
       _  -> addToContent (addToContent st $ genNormalResponse msgtxt) $
                      genErrorResponse False errmsg
     else addToMsg msgtxt errmsg st

-- | It inserts a given string into the XML packet as
-- error output
genErrAnswer :: String -> CMDL_PgipState -> CMDL_PgipState
genErrAnswer  str st
 = case str of
    [] -> st
    _ -> if useXML st
          then addToContent st $ genErrorResponse True str
          else addToMsg [] str st

-- | Executes given commands and returns output message and the new state
processCmds :: [CMDL_XMLcommands] -> CMDL_State -> CMDL_PgipState ->
              IO (CMDL_State, CMDL_PgipState)
processCmds cmds state pgipState
 = do
    let pgipSt = pgipState --{resendMsgIfTimeout = False,
                           -- maxWaitTime = 2000}
--    putStrLn $ show state
    case cmds of
     [] -> if useXML pgipSt
            -- ensures that the response is ended with a ready element
            -- such that the broker does wait for more input
            then return (state, addReadyXml pgipSt )
            else return (state, pgipSt)
     (XML_Execute str):l -> do
                           --  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                           --  hFlush $ hout pgipSt
                             let nPGIP = resetMsg [] pgipSt
                             -- process string line
                             nwSt <- cmdlProcessString str state
                             case errorMsg $ output nwSt of
                              [] -> processCmds l nwSt $
                                     genAnswer (outputMsg $ output nwSt)
                                               (warningMsg $ output nwSt)
                                               nPGIP
                              _ -> return (nwSt, genErrAnswer
                                              (errorMsg $ output nwSt) nPGIP)
     XML_Exit :l ->
                  processCmds l state $ genAnswer "Exiting prover" []
                                           pgipSt { stop = True }
     XML_Askpgip:_ ->
                  if useXML pgipSt
                   then return (state,  genHandShake pgipSt)
                   else return (state, resetMsg []  pgipSt)
     XML_ProverInit :l ->
                  processCmds l emptyCMDL_State $ genAnswer
                          "Prover state was reseted" [] pgipSt
     XML_StartQuiet :l ->
                  -- Quiet not yet implemented !!
                  processCmds l state $ genAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = True }
     XML_StopQuiet :l ->
                  -- Quiet not yet implemented !!
                  -- use proper tmp-files and avoid duplicate code!
                  processCmds l state $ genAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = False }
     (XML_OpenGoal str) :l -> do
                  nwSt <- cmdlProcessString ("add goals "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                           genAnswer (outputMsg $ output nwSt)
                                    (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                         pgipSt)
     (XML_CloseGoal str) :l -> do
                  nwSt <- cmdlProcessString ("del goals "++str++"\n prove \n")
                                                                     state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      pgipSt)
     (XML_GiveUpGoal str) :l -> do
                  nwSt <- cmdlProcessString ("del goals "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      pgipSt)
     (XML_Unknown str) :_ ->
                  return (state, genAnswer []  ("Unknown command : "++str)
                                        pgipSt)
     XML_Undo : l -> do
                  nwSt <- cmdlProcessString "undo \n" state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     pgipSt)
     XML_Redo : l -> do
                  nwSt <- cmdlProcessString "redo \n" state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     pgipSt)
     (XML_Forget str) :l -> do
                  nwSt <- cmdlProcessString ("del axioms "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                    pgipSt)
     (XML_OpenTheory str) :l -> do
                  nwSt <- cmdlProcessString ("select "++str ++ "\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> processCmds [] nwSt $ genErrAnswer
                                    (errorMsg $ output nwSt) pgipSt
     (XML_CloseTheory _) :l ->
                  case i_state $ intState state of
                   Nothing ->
                     processCmds l state (genAnswer "Theory closed" [] pgipSt)
                   Just ist -> do
                     let nwSt =
                          add2hist [IStateChange $ Just ist] $
                               state {
                                intState = (intState state) {
                                  i_state = Just $ emptyIntIState
                                             (i_libEnv ist) (i_ln ist)
                                             }
                                }
                     processCmds l nwSt (genAnswer "Theory closed" [] pgipSt)
     (XML_CloseFile _) :l ->
                  processCmds l emptyCMDL_State (genAnswer "File closed" []
                                                       pgipSt)
     (XML_ParseScript str) : _ ->
                 processCmds [] state $ addToContent pgipSt (addPgipMarkUp str)
     (XML_LoadFile str) : l -> do
                  nwSt <- cmdlProcessString ("use "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                       pgipSt)

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

import Network
import System.IO

import PGIP.XMLstate
import PGIP.Interface
import PGIP.DataTypes
import Data.List
import Interfaces.DataTypes
import Interfaces.Utils
import PGIP.DataTypesUtils
import qualified Text.XML.Light.Types as XmlT
import Text.XML.Light.Output

-- | Generates the XML packet that contains information about the interface
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
              el_askpgip
            : el_askpgml
            : el_askprefs
            : el_getprefs
            : el_setprefs
            : el_proverinit
            : el_proverexit
            : el_startquiet
            : el_stopquiet
            : el_pgmlsymbolon
            : el_pgmlsymboloff
            : el_dostep
            : el_undostep
            : el_redostep
            : el_abortgoal
            : el_forget
            : el_restoregoal
            : el_askids
            : el_showid
            : el_askguise
            : el_parsescript
            : el_showproofstate
            : el_showctxt
            : el_searchtheorems
            : el_setlinewidth
            : el_viewdoc
            : el_doitem
            : el_undoitem
            : el_redoitem
            : el_aborttheory
            : el_retracttheory 
            : el_loadfile
            : el_openfile
            : el_closefile
            : el_abortfile
            : el_changecwd
            : el_systemcmd
            : []
       xmlrootElem = XmlT.Elem $ XmlT.blank_element {
         XmlT.elName = genQName "usespgip",
         XmlT.elAttribs = [XmlT.Attr { XmlT.attrKey = genQName "version",
                                       XmlT.attrVal = "2.0" } ],
         XmlT.elContent = [
            XmlT.Elem $ XmlT.Element { 
                    XmlT.elName    = genQName "acceptedpgipelems",
                    XmlT.elAttribs = [],
                    XmlT.elContent = pgip_elems,
                    XmlT.elLine    = Nothing } ],
         XmlT.elLine = Nothing }
   in case useXML pgipData of
       True -> addToContent pgipData xmlrootElem 
       False -> pgipData

-- | The function executes a communication step, i.e. waits for input,
-- processes the message and outputs the answer
communicationStep:: CMDL_PgipState -> CMDL_State ->
                     IO (CMDL_PgipState, CMDL_State)
communicationStep pgD st =
  do
   tmp <- timeoutReadPacket (maxWaitTime pgD) pgD
   appendFile "/tmp/razvan.txt" ("Input : "++(show tmp)++"\n")
   case tmp of
    Nothing -> case resendMsgIfTimeout pgD of
                True -> do
                         -- appendFile "/tmp/razvan.txt" ("Output : "++
                         --                      (theMsg pgD) ++ "\n")
                         hPutStrLn (hout pgD) $ theMsg pgD
                         hFlush $ hout pgD
                         communicationStep pgD st
                False -> communicationStep pgD st
    Just smtxt -> do
                   appendFile "/tmp/razvan.txt" "Processing input"
                   cmds <- parseMsg pgD smtxt
                   (nwSt, nwPgD) <-processCmds cmds st $ resetMsg [] pgD
                   let nwPgipSt = case useXML pgD of
                                   True ->
                                    addToMsg (showContent $ xmlContent nwPgD)
                                                     [] nwPgD
                                   False -> nwPgD
                   appendFile "/tmp/razvan.txt" ("Output : "++ (theMsg pgD)++
                                                       "\n")
                   hPutStrLn (hout pgD) $ theMsg nwPgipSt
                   hFlush $ hout pgD
                   return (nwPgipSt, nwSt)


-- | Comunicates over a port at which the prover should listen
cmdlListen2Port :: Bool -> Int -> IO CMDL_State
cmdlListen2Port swXML portNb
 = do
    putStrLn("Starting hets. Listen to port "++(show portNb))
    servSock <- listenOn $ PortNumber (fromIntegral portNb)
    (servH,_,_) <- accept servSock
    pgData <- genCMDL_PgipState swXML servH servH
    let pgD = case swXML of
               True -> addReadyXml
                       $ genHandShake
                       $ resetMsg [] pgData
               False -> resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
      do
       (nwpgD,nwSt) <- communicationStep pgipD st
       case stop nwpgD of
        False -> waitLoop nwpgD nwSt
        True -> return nwSt

-- | Comunicates over a port to which the prover has to connect
cmdlConnect2Port :: Bool -> String -> Int -> IO CMDL_State
cmdlConnect2Port swXML hostName portNb
 = do
    putStrLn ("Starting hets. Connecting to port "++(show portNb))
    sockH <- connectTo hostName $ PortNumber (fromIntegral portNb)
    pgData <- genCMDL_PgipState swXML sockH sockH
    let pgD = case swXML of
               True -> addReadyXml
                       $ genHandShake
                       $ resetMsg [] pgData
               False -> resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
      do
       (nwpgD,nwSt) <- communicationStep pgipD st
       case stop nwpgD of
        False -> waitLoop nwpgD nwSt
        True -> return nwSt


-- | Reads from a handle, it waits only for a certain amount of time,
-- if no input comes it will return Nothing
timeoutReadPacket :: Int -> CMDL_PgipState -> IO (Maybe String)
timeoutReadPacket untilTimeout st
 = do
    smtmp <- hWaitForInput (hin st) untilTimeout
    case smtmp of
     True -> do
              ms <- case useXML st of
                     True -> readPacket [] $ hin st
                     False -> hGetLine $ hin st
              return $ Just ms
     False -> return Nothing

-- | Waits until it reads an entire XML packet
readPacket :: String -> Handle -> IO String
readPacket acc hf
 = do
    tmp <- hGetLine hf
    case isInfixOf "</pgip>" tmp of
      True -> return (acc++tmp++"\n")
      False -> readPacket (acc++tmp++"\n") hf

-- | Runs a shell in which the communication is expected to be
-- through XML packets
cmdlRunXMLShell :: IO CMDL_State
cmdlRunXMLShell
 = do
    pgData <- genCMDL_PgipState True stdin stdout
    let pgD = addReadyXml
              $ genHandShake
              $ resetMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
       do
        (nwpgD,nwSt) <- communicationStep pgipD st
        case stop nwpgD of
         False -> waitLoop nwpgD nwSt
         True -> return nwSt

-- | It inserts a given string into the XML packet as
-- normal output
genAnswer :: String -> String -> CMDL_PgipState -> CMDL_PgipState
genAnswer msgtxt errmsg st
 = case useXML st of
     True ->  
      case errmsg of
       [] -> addToContent st $ genNormalResponse $ msgtxt 
       _  -> addToContent (addToContent st $ genNormalResponse msgtxt) $
                      genErrorResponse False $ errmsg
     False -> addToMsg msgtxt errmsg st

-- | It inserts a given string into the XML packet as
-- error output
genErrAnswer :: String -> CMDL_PgipState -> CMDL_PgipState
genErrAnswer  str st
 = case str of
    [] -> st
    _ -> case useXML st of
          True ->
           addToContent st $ genErrorResponse True str
          False -> addToMsg [] str st

-- | Executes given commands and returns output message and the new state
processCmds :: [CMDL_XMLcommands] -> CMDL_State -> CMDL_PgipState ->
              IO (CMDL_State, CMDL_PgipState)
processCmds cmds state pgipState
 = do
    let pgipSt = pgipState {resendMsgIfTimeout = False,
                            maxWaitTime = 2000}
    case cmds of
     [] -> case useXML pgipSt of
            True -> return (state, addReadyXml pgipSt )
            False -> return (state, pgipSt)
     (XML_Execute str):l -> do
                           --  appendFile "/tmp/razvan.txt" ("Output : "++
                           --                      (theMsg pgipSt)++"\n")
                           --  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                           --  hFlush $ hout pgipSt
                             let nPGIP = resetMsg [] pgipSt
                             appendFile "/tmp/razvan.txt" ("\n\n" ++ str)
                             nwSt <- cmdlProcessString str state
                             case errorMsg $ output nwSt of
                              [] -> processCmds l nwSt $
                                     genAnswer (outputMsg $ output nwSt) 
                                               (warningMsg $ output nwSt)
                                               nPGIP
                              _ -> return (nwSt, genErrAnswer
                                              (errorMsg $ output nwSt) nPGIP)
     XML_Exit :l -> do
                  processCmds l state $ genAnswer "Exiting prover" []
                                           pgipSt { stop = True }
     XML_Askpgip:_ -> do
                  case useXML pgipSt of
                   True -> return (state,  genHandShake pgipSt)
                   False -> return (state, resetMsg []  pgipSt)
     XML_ProverInit :l -> do
                  processCmds l emptyCMDL_State $ genAnswer
                          "Prover state was reseted" [] pgipSt
     XML_StartQuiet :l -> do
                  -- Quiet not yet implemented !!
                  processCmds l state $ genAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = True }
     XML_StopQuiet :l -> do
                  -- Quiet not yet implemented !!
                  processCmds l state $ genAnswer
                        "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = False }
     (XML_OpenGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                         ++"\n")
                  nwSt <- cmdlProcessString ("add goals "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                           genAnswer (outputMsg $ output nwSt)
                                    (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                         pgipSt)
     (XML_CloseGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : " ++(theMsg pgipSt)
                                                         ++"\n")
                  nwSt <- cmdlProcessString ("add goals "++str++"\n prove \n")
                                                                     state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      pgipSt)
     (XML_GiveUpGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                    ++"\n")
                  nwSt <- cmdlProcessString ("del goals "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      pgipSt)
     (XML_Unknown str) :_ -> do
                  return (state, genAnswer []  ("Unknown command : "++str)
                                        pgipSt)
     XML_Undo : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                           ++ "\n")
                  nwSt <- cmdlProcessString ("undo \n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     pgipSt)
     XML_Redo : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                     ++ "\n")
                  nwSt <- cmdlProcessString ("redo \n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     pgipSt)
     (XML_Forget str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                         ++ "\n")
                  nwSt <- cmdlProcessString ("del axioms "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                    pgipSt)
     (XML_OpenTheory str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                        ++"\n")
                  nwSt <- cmdlProcessString ("select "++str ++ "\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                    pgipSt)
     (XML_CloseTheory _) :l -> do
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
     (XML_CloseFile _) :l -> do
                  processCmds l emptyCMDL_State (genAnswer "File closed" []
                                                       pgipSt)
     (XML_LoadFile str) : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                          ++ "\n")
                  nwSt <- cmdlProcessString ("use "++str++"\n") state
                  case errorMsg $ output nwSt of
                   [] -> processCmds l nwSt $
                          genAnswer (outputMsg $ output nwSt)
                                   (warningMsg $ output nwSt) pgipSt
                   _ -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                       pgipSt)

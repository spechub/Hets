{- |
Module      :$Header$
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
-- import Control.Exception

import PGIP.XMLstate
import PGIP.Interface
import PGIP.DataTypes
import Data.List


-- | Generates the XML packet that contains information about the interface
genHandShake :: CMDL_PgipState -> CMDL_PgipState
genHandShake pgipData
 =
   let msg = ( "<usespgip version = \"2.0\">"++
               "<acceptedpgipelems>"++
               "<pgipelem>askpgip</pgipelem>"++
               "<pgipelem>askpgml</pgipelem>"++
               "<pgipelem>askprefs</pgipelem>"++
               "<pgipelem>getpref</pgipelem>"++
               "<pgipelem>setpref</pgipelem>"++
               "<pgipelem>proverinit</pgipelem>"++
               "<pgipelem>proverexit</pgipelem>"++
               "<pgipelem>startquiet</pgipelem>"++
               "<pgipelem>stopquiet</pgipelem>"++
               "<pgipelem>pgmlsymbolson</pgipelem>"++
               "<pgipelem>pgmlsymbolsoff</pgipelem>"++
               "<pgipelem>dostep</pgipelem>"++
               "<pgipelem>undostep</pgipelem>"++
               "<pgipelem>redostep</pgipelem>"++
               "<pgipelem>abortgoal</pgipelem>"++
               "<pgipelem>forget</pgipelem>"++
               "<pgipelem>restoregoal</pgipelem>"++
               "<pgipelem>askids</pgipelem>"++
               "<pgipelem>showid</pgipelem>"++
               "<pgipelem>askguise</pgipelem>"++
               "<pgipelem>parsescript</pgipelem>"++
               "<pgipelem>showproofstate</pgipelem>"++
               "<pgipelem>showctxt</pgipelem>"++
               "<pgipelem>searchtheorems</pgipelem>"++
               "<pgipelem>setlinewidth</pgipelem>"++
               "<pgipelem>viewdoc</pgipelem>"++
               "<pgipelem>doitem</pgipelem>"++
               "<pgipelem>undoitem</pgipelem>"++
               "<pgipelem>redoitem</pgipelem>"++
               "<pgipelem>abortheory</pgipelem>"++
               "<pgipelem>retracttheory</pgipelem>"++
               "<pgipelem>loadfile</pgipelem>"++
               "<pgipelem>openfile</pgipelem>"++
               "<pgipelem>closefile</pgipelem>"++
               "<pgipelem>abortfile</pgipelem>"++
               "<pgipelem>changecwd</pgipelem>"++
               "<pgipelem>systemcmd</pgipelem>"++
               " </acceptedpgipelems>"++
               "</usespgip>")
   in case useXML pgipData of
       True -> addToMsg msg [] pgipData
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
                         appendFile "/tmp/razvan.txt" ("Output : "++
                                               (theMsg pgD) ++ "\n")
                         hPutStrLn (hout pgD) $ theMsg pgD
                         hFlush $ hout pgD
                         communicationStep pgD st
                False -> communicationStep pgD st
    Just smtxt -> do
                   cmds <- parseMsg pgD smtxt
                   let pgipSt = case useXML pgD of
                                 True ->
                                   addToMsg "<normalresponse></pgmltext>" []$
                                   genPgipTag $ resetMsg [] pgD{
                                                      seqNb = (seqNb pgD)+1,
                                                      nonFatalErrMsg = []
                                                       }
                                 False -> resetMsg [] pgD{
                                                       seqNb = (seqNb pgD)+1,
                                                       nonFatalErrMsg = []
                                                       }
                   (nwSt, nwPgipState) <- processCmds cmds st pgipSt
                   let nwPgipSt = case useXML pgD of
                                   True ->
                                    addToMsg "<ready/></pgip>" [] nwPgipState
                                   False -> nwPgipState
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
               True -> addToMsg "<ready/></pgip>" []
                       $ genHandShake
                       $ genPgipTag
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
               True -> addToMsg "<ready/></pgip>" []
                       $ genHandShake
                       $ genPgipTag
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
      True -> return (acc++tmp)
      False -> readPacket (acc++tmp) hf

-- | Runs a shell in which the communication is expected to be
-- through XML packets
cmdlRunXMLShell :: IO CMDL_State
cmdlRunXMLShell
 = do
    pgData <- genCMDL_PgipState True stdin stdout
    let pgD = addToMsg "<ready/></pgip>" []
              $ genHandShake
              $ genPgipTag
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
genAnswer :: CMDL_PgipState -> CMDL_PgipState
genAnswer st
 = case useXML st of
     True -> case nonFatalErrMsg st of
              [] -> st {
                      theMsg = (theMsg st) ++ "</pgmltext></normalresponse>"
                      }
              _ -> st {
                     theMsg = (theMsg st) ++ "</pgmltext></normalresponse>" ++
                        "<errorresponse fatality=\"nonfatal\">"++
                        "<pgmltext>"++ (nonFatalErrMsg st) ++
                        "</pgmltext></errorresponse>"
                        }
     False -> case nonFatalErrMsg st of
               [] -> st
               stxt -> st {
                       theMsg = (theMsg st)++"\n"++stxt
                       }

-- | It inserts a given string into the XML packet as
-- error output
genErrAnswer :: String -> CMDL_PgipState -> CMDL_PgipState
genErrAnswer  str st
 = case str of
    [] -> st
    _ -> case useXML st of
          True ->addToMsg ("</pgmltext></normalresponse>"++
                           "<errorresponse fatality=\"fatal\"><pgmltext>"++
                           str++"</pgmltext></errorresponse>") [] st
          False -> addToMsg str [] st

-- | Executes given commands and returns output message and the new state
processCmds :: [CMDL_XMLcommands] -> CMDL_State -> CMDL_PgipState ->
              IO (CMDL_State, CMDL_PgipState)
processCmds cmds state pgipState
 = do
    let pgipSt = pgipState {resendMsgIfTimeout = False,
                            maxWaitTime = 2000}
    case cmds of
     [] -> case useXML pgipSt of
            True -> return (state, genAnswer pgipSt )
            False -> return (state, pgipSt)
     (XML_Execute str):l -> do
                             appendFile "/tmp/razvan.txt" ("Output : "++
                                                 (theMsg pgipSt)++"\n")
                             hPutStrLn (hout pgipSt) $ theMsg pgipSt
                             hFlush $ hout pgipSt
                             let nPGIP = resetMsg [] pgipSt
                             nwSt <- cmdlProcessString str state
                             case fatalError $ output nwSt of
                              False -> processCmds l nwSt $
                                         addToMsg (outputMsg $ output nwSt)
                                                  (errorMsg $ output nwSt)
                                                  nPGIP
                              True -> return (nwSt, genErrAnswer
                                              (errorMsg $ output nwSt) nPGIP)
     XML_Exit :l -> do
                  processCmds l state $ addToMsg "Exiting prover" []
                                           pgipSt { stop = True }
     XML_Askpgip:_ -> do
                  case useXML pgipSt of
                   True -> return (state,  genHandShake
                                          $ genPgipTag
                                          $ resetMsg [] pgipSt)
                   False -> return (state, resetMsg []  pgipSt)
     XML_ProverInit :l -> do
                  processCmds l emptyCMDL_State $ addToMsg
                          "Prover state was reseted" [] pgipSt
     XML_StartQuiet :l -> do
                  -- Quiet not yet implemented !!
                  processCmds l state $
                       addToMsg "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = True }
     XML_StopQuiet :l -> do
                  -- Quiet not yet implemented !!
                  processCmds l state $
                       addToMsg "Quiet mode doesn't work properly" [] pgipSt {
                                              quietOutput = False }
     (XML_OpenGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                         ++"\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("add goals "++str++"\n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                           addToMsg (outputMsg $ output nwSt)
                                    (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                         nPGIP)
     (XML_CloseGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : " ++(theMsg pgipSt)
                                                         ++"\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("add goals "++str++"\n prove \n")
                                                                     state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      nPGIP)
     (XML_GiveUpGoal str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                    ++"\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("del goals "++str++"\n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      nPGIP)
     (XML_Unknown str) :_ -> do
                  return (state, addToMsg []  ("Unknown command : "++str)
                                        pgipSt)
     XML_Undo : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                           ++ "\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("undo \n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     nPGIP)
     XML_Redo : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                     ++ "\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("redo \n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                     nPGIP)
     (XML_Forget str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                         ++ "\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("del axioms "++str++"\n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                    nPGIP)
     (XML_OpenTheory str) :l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                        ++"\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("select "++str ++ "\n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                    nPGIP)
     (XML_CloseTheory _) :l -> do
                  let hst = history state
                      uI  = undoInstances hst
                      nwSt = state {
                                proveState = Nothing,
                                history = hst {
                                          undoInstances = ([],[]): uI
                                          }
                                }
                  processCmds l nwSt $ addToMsg "Theory closed" [] pgipSt
     (XML_CloseFile _) :l -> do
                  processCmds l emptyCMDL_State $ addToMsg "File closed" []
                                                       pgipSt
     (XML_LoadFile str) : l -> do
                  appendFile "/tmp/razvan.txt" ("Output : "++(theMsg pgipSt)
                                                          ++ "\n")
                  hPutStrLn (hout pgipSt) $ theMsg pgipSt
                  hFlush $ hout pgipSt
                  let nPGIP = resetMsg [] pgipSt
                  nwSt <- cmdlProcessString ("use "++str++"\n") state
                  case fatalError $ output nwSt of
                   False -> processCmds l nwSt $
                          addToMsg (outputMsg $ output nwSt)
                                   (errorMsg $ output nwSt) nPGIP
                   True -> return (nwSt, genErrAnswer (errorMsg $ output nwSt)
                                      nPGIP)

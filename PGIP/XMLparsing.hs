{- |
Module      :$Header$
Description : XML processing for the CMDL interface
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.XMLparsing contains commands for parsing or creating XML messages
-}

module PGIP.XMLparsing
where

import Network
import System.IO
import Control.Exception

import PGIP.XMLstate
import PGIP.Interface
import PGIP.DataTypes
import Data.List


genHandShake :: PGIP_STATE -> PGIP_STATE
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
   in addXmlMsg msg pgipData


communicationStep:: PGIP_STATE -> CMDL_State -> IO (PGIP_STATE, CMDL_State)
communicationStep pgD st =
  do
   hPutStrLn (hout pgD) $ xmlMsg pgD
   hFlush $ hout pgD
   tmp <- readPacket [] $ hin pgD
   (nwSt, tmp',c) <- talk2Broker tmp st
   let nwpgD = addXmlMsg "<ready/></pgip>"
               $ addXmlMsg tmp'
               $ genPgipTag
               $ resetXmlMsg [] pgD {
                                 seqNb = (seqNb pgD) + 1,
                                 stop = c
                                 }
   return (nwpgD, nwSt)


cmdlListen2Port :: Int -> IO CMDL_State
cmdlListen2Port portNb
 = do
    putStrLn("Starting hets. Listen to port "++(show portNb))
    servSock <- listenOn $ PortNumber (fromIntegral portNb)
    waitLoop servSock emptyCMDL_State
   where
    waitLoop servSock st =
      do
       (cont,nSt) <- bracket ( do
                                (servH,_,_) <- accept servSock
                                --pgData <- genPGIP_STATE servH servH
                                return servH)
--                                return $ addXmlMsg "<ready/></pgip>"
--                                       $ genHandShake
--                                       $ genPgipTag
--                                       $ resetXmlMsg [] pgData)
                     hClose
                     (\_ -> return (False,st)) -- comunicationStep h st)
       case  cont of
        True -> waitLoop servSock nSt
        False -> do
                  sClose servSock
                  return nSt

cmdlConnect2Port :: Int -> IO CMDL_State
cmdlConnect2Port portNb
 = do
    putStrLn ("Starting hets. Connecting to port "++(show portNb))
    sockH <- connectTo "localhost" $ PortNumber (fromIntegral portNb)
    waitLoop sockH emptyCMDL_State
   where
    waitLoop sockH st =
      do
       (cont,nSt) <- bracket ( do
                                -- hPutStr sockH handShake
                                return sockH)
                     hClose
                     (\_ -> return (False,st)) -- comunicationStep h st)
       case cont of
        True -> waitLoop sockH nSt
        False -> do
                  hClose sockH
                  return nSt



readPacket :: String -> Handle -> IO String
readPacket acc hf
 = do
    tmp <- hGetLine hf
    case isInfixOf "</pgip>" tmp of
     True -> return (acc++tmp)
     False -> readPacket (acc++tmp) hf

cmdlRunXMLShell :: IO CMDL_State
cmdlRunXMLShell
 = do
    pgData <- genPGIP_STATE stdin stdout
    let pgD = addXmlMsg "</pgip>"
              $ genHandShake
              $ genPgipTag
              $ resetXmlMsg [] pgData
    waitLoop pgD emptyCMDL_State
   where
    waitLoop pgipD st =
       do
        (nwpgD,nwSt) <- communicationStep pgipD st
        case stop nwpgD of
         False -> waitLoop nwpgD nwSt
         True -> return nwSt

talk2Broker :: String -> CMDL_State -> IO (CMDL_State, String, Bool)
talk2Broker pck state
 =
   do
    cmds <- parseXMLString pck
    (nwSt, answ,c) <- processCmds cmds state
    return (nwSt,answ,c)


processCmd :: [CMDL_XMLstate] -> CMDL_State -> String -> Bool ->
              IO (CMDL_State, String, Bool)
processCmd cmds state answ c
 = case cmds of
     [] -> return (state,answ,c)
     (XML_Execute str):l -> do
                  nwSt <- cmdlProcessString str state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")
                  processCmd l nwSt nwAnsw' c
     XML_Exit :l -> do
                  processCmd l state answ True
     XML_ProverInit :l -> do
                  processCmd l emptyCMDL_State answ c
     XML_StartQuiet :l -> do
                  processCmd l state answ c
     XML_StopQuiet :l -> do
                  processCmd l state answ c
     (XML_OpenGoal str) :l -> do
                  nwSt <- cmdlProcessString ("add goals "++str++"\n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_CloseGoal str) :l -> do
                  nwSt <- cmdlProcessString ("add goals "++str++"\n prove \n")
                                                                     state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_GiveUpGoal str) :l -> do
                  nwSt <- cmdlProcessString ("del goals "++str++"\n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_Unknown _) :l -> do
                  processCmd l state answ c
     XML_Undo : l -> do
                  nwSt <- cmdlProcessString ("undo \n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     XML_Redo : l -> do
                  nwSt <- cmdlProcessString ("redo \n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_Forget str) :l -> do
                  nwSt <- cmdlProcessString ("del axioms "++str++"\n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_OpenTheory str) :l -> do
                  nwSt <- cmdlProcessString ("select "++str ++ "\n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c
     (XML_CloseTheory _) :l -> do
                  let hst = history state
                      uI  = undoInstances hst
                      nwSt = state {
                                proveState = Nothing,
                                history = hst {
                                          undoInstances = ([],[]): uI
                                          }
                                }
                  processCmd l nwSt answ c
     (XML_CloseFile _) :l -> do
                  processCmd l emptyCMDL_State answ c
     (XML_LoadFile str) : l -> do
                  nwSt <- cmdlProcessString ("use "++str++"\n") state
                  let nwAnsw = case errorMsg $ output nwSt of
                                 [] -> answ
                                 err -> ( answ++"<errorresponse>"++
                                            err ++ "</errorresponse>")
                  let nwAnsw' = case outputMsg $ output nwSt of
                                 [] -> nwAnsw
                                 msg -> (nwAnsw++"<normalresponse>"++
                                             msg++"</normalresponse>")

                  processCmd l nwSt nwAnsw' c


processCmds::[CMDL_XMLstate] -> CMDL_State -> IO (CMDL_State, String, Bool)
processCmds cmds state
 = do
    (nwSt,nwAnsw,c) <- processCmd cmds state [] False
    return (nwSt, nwAnsw,c)



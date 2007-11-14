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

interactTCP :: Int-> (String ->CMDL_State ->IO (CMDL_State,String))
               -> IO CMDL_State
interactTCP port f = withSocketsDo $ do
        servSock <- listenOn $ PortNumber (fromIntegral port)
        lSt <- waitLoop f servSock emptyCMDL_State
        return lSt

waitLoop::(String ->CMDL_State -> IO (CMDL_State,String)) -> Socket 
           -> CMDL_State -> IO CMDL_State
waitLoop f servSock st = do
       nSt <- bracket (fmap (\(h,_,_) -> h) $ accept servSock)
                      hClose
                      (\h -> do 
                              hSetBuffering h LineBuffering
                              tmp  <- hGetContents h 
                              (nwSt,tmp') <- f tmp st
                              hPutStr h tmp'
                              return nwSt
                      )
       waitLoop f servSock nSt

cmdlConnect2Port :: Int -> IO CMDL_State
cmdlConnect2Port portNb
 = do
    lSt <- interactTCP portNb talk2Broker
    return lSt

talk2Broker :: String -> CMDL_State -> IO (CMDL_State, String)
talk2Broker pck state
 = 
   do 
    cmds <- parseXMLString pck
    (nwSt, answ) <- processCmds cmds state
    return (nwSt,answ)


processCmd :: [CMDL_XMLstate] -> CMDL_State -> String -> 
              IO (CMDL_State, String)
processCmd cmds state answ
 = case cmds of
     [] -> return (state,answ)
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
                  processCmd l nwSt nwAnsw'
     XML_Exit :l -> do
                  processCmd l state answ
     XML_ProverInit :l -> do
                  processCmd l emptyCMDL_State answ
     XML_StartQuiet :l -> do
                  processCmd l state answ
     XML_StopQuiet :l -> do
                  processCmd l state answ
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
                  
                  processCmd l nwSt nwAnsw'
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
                  
                  processCmd l nwSt nwAnsw'
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
                  
                  processCmd l nwSt nwAnsw'
     (XML_Unknown _) :l -> do
                  processCmd l state answ
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
                 
                  processCmd l nwSt nwAnsw'
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
                  
                  processCmd l nwSt nwAnsw'
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
                  
                  processCmd l nwSt nwAnsw'
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
                 
                  processCmd l nwSt nwAnsw'
     (XML_CloseTheory _) :l -> do
                  let hst = history state
                      uI  = undoInstances hst 
                      nwSt = state {
                                proveState = Nothing,
                                history = hst {
                                          undoInstances = ([],[]): uI
                                          }
                                }
                  processCmd l nwSt answ
     (XML_CloseFile _) :l -> do
                  processCmd l emptyCMDL_State answ
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
                  
                  processCmd l nwSt nwAnsw'
 

processCmds::[CMDL_XMLstate] -> CMDL_State -> IO (CMDL_State, String)
processCmds cmds state
 = do
    let answ = "<pgip>"
    (nwSt,nwAnsw) <- processCmd cmds state answ
    let answ' = nwAnsw ++ "<ready/></pgip>"
    return (nwSt, answ')
   


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

interactTCP :: Int-> (String ->CMDL_State ->IO (CMDL_State,String,Bool))
               -> IO CMDL_State
interactTCP port f = withSocketsDo $ do
        servSock <- connectTo "localhost" $ PortNumber (fromIntegral port)
        lSt <- waitLoop f servSock emptyCMDL_State
        return lSt

waitLoop::(String ->CMDL_State -> IO (CMDL_State,String,Bool)) -> Handle
           -> CMDL_State -> IO CMDL_State
waitLoop f servSock st = do
       (cont,nSt) <- bracket (do
                               hPutStrLn servSock "<pgip><ready/></pgip>"
                               return servSock)
                      hClose
                      (\h -> do
                              hSetBuffering h LineBuffering
                              tmp  <- hGetContents h
                              putStrLn tmp
                              (nwSt,tmp',c) <- f tmp st
                              hPutStr h tmp'
                              return (c,nwSt)
                      )
       case cont of
         True -> waitLoop f servSock nSt
         False -> do
                   hClose servSock
                   return nSt

cmdlConnect2Port :: Int -> IO CMDL_State
cmdlConnect2Port portNb
 = do
    putStrLn ("Starting hets with port " ++ (show portNb))
    lSt <- interactTCP portNb talk2Broker
    return lSt

talk2Broker :: String -> CMDL_State -> IO (CMDL_State, String, Bool)
talk2Broker pck state
 =
   do
    putStrLn ("PCK :: " ++pck)
    cmds <- parseXMLString pck
    putStrLn $ show cmds
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
                  processCmd l state answ False
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
    let answ = "<pgip>"
    (nwSt,nwAnsw,c) <- processCmd cmds state answ True
    let answ' = nwAnsw ++ "<ready/></pgip>"
    return (nwSt, answ',c)



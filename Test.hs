module Test

where

import System.Environment
import Comorphisms.LogicGraph
import Static.AnalysisLibrary
import System.IO
import Static.DotGraph
import Static.DevGraph
import Options
import CASL.Logic_CASL
import Common.Lib.Graph
import Logic.Logic
import Logic.Grothendieck
import Common.Result
import Common.Id
import Common.AS_Annotation

--proceed :: String -> IO()
proceed fname = do
  anaFile logicGraph defaultLogic defaultHetcatsOpts emptyLibEnv fname
{-  case res of
    Just(_,_,dg,_) -> do
      putStrLn ("Successfully analyzed.")
      putStrLn ("Writing development graph to "++fname++".dot")
      h <- openFile (fname++".dot") WriteMode
      sequence (map (hPutStrLn h) (dot dg))
      hClose h
    _ -> return ()
-}

getCASLSig :: String -> IO CASLSign
getCASLSig fname = do
  res <- proceed fname
  case res of
    Just (_,_,dg,_) -> do
      case match 1 dg of
        (Just ctx,_) -> case dgn_sign $ lab' ctx of
          G_sign lid sig ->
            case maybeResult $ rcoerce lid CASL nullPos sig of
               Just sig' -> return sig'
               Nothing -> error "Not a CASL sig"
        _ -> error "Node 1 no in development graph" 
    Nothing -> error "Error occured"

getCASLSens :: String -> IO [Named CASLFORMULA]
getCASLSens fname = do
  res <- proceed fname
  case res of
    Just (_,_,dg,_) -> do
      case match 1 dg of
        (Just ctx,_) -> case dgn_sens $ lab' ctx of
          G_l_sentence_list lid sens ->
            case maybeResult $ rcoerce lid CASL nullPos sens of
               Just sens' -> return sens'
               Nothing -> error "Not the CASL logic"
        _ -> error "Node 1 no in development graph" 
    Nothing -> error "Error occured"

main :: IO()
main = do
  files <- getArgs
  sequence (map proceed files)
  return ()



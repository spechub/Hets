module Main

where

import System.Environment
import Comorphisms.LogicGraph
import Static.AnalysisLibrary
import System.IO
import Static.DotGraph
import Static.DevGraph
import Options

proceed :: String -> IO()
proceed fname = do
  res <- anaFile logicGraph defaultLogic defaultHetcatsOpts emptyLibEnv fname
  case res of
    Just(_,_,dg,_) -> do
      putStrLn ("Successfully analyzed.")
      putStrLn ("Writing development graph to "++fname++".dot")
      h <- openFile (fname++".dot") WriteMode
      sequence (map (hPutStrLn h) (dot dg))
      hClose h
    _ -> return ()

main :: IO()
main = do
  files <- getArgs
  sequence (map proceed files)
  return ()



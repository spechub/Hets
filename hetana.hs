module Main

where

import System
import LogicGraph
import AnalysisLibrary
import IO
import DotGraph

proceed :: String -> IO()
proceed fname = do
  putStrLn ("Reading "++fname)
  res <- ana_file1 logicGraph defaultLogic fname
  case res of
    Nothing -> putStrLn ("Errors occured.")
    Just (_,dg,_) -> do
      putStrLn ("Successfully analyzed.")
      putStrLn ("Writing development graph to "++fname++".dot")
      h <- openFile (fname++".dot") WriteMode
      sequence (map (hPutStrLn h) (dot dg))
      hClose h


main :: IO()
main = do
  files <- getArgs
  sequence (map proceed files)
  return ()



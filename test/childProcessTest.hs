module Main where

import ChildProcess
import Computation
import Concurrent

main = do
  p <- newChildProcess "isabelle" [arguments ["HOL"]]
  sendMsg p "3+4;"
  forkIO $ forever $ readMsg p >>= putStrLn
  return p

module Main where

import ChildProcess
import Computation
import Concurrent

main = do
  p <- newChildProcess "isabelle" [arguments ["HOL"]]
  sendMsg p "3+4;"
  forkIO $ forever $ do m <- readMsg p; putStrLn m
  return p

{- |
Module      :  $Header$
Description :  get the output from a childProcess
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

get the output from a childProcess
-}

module Propositional.ChildMessage (parseIt) where

import Common.UniUtils
import System.Exit

parseIt :: ChildProcess -> (String -> Bool) -> IO String
parseIt cp isEnd = do
  line <- readMsg cp
  ls  <- parseItHelp cp isEnd [line]
  return $ unlines $ reverse ls

-- | Helper function for parsing cp output
parseItHelp :: ChildProcess -> (String -> Bool) -> [String] -> IO [String]
parseItHelp cp isEnd inT = do
  e <- getToolStatus cp
  case e of
    Just (ExitFailure _) -> return inT
    _ -> do
      line <- readMsg cp
      let out = line : inT
      if isEnd line then do
         waitForChildProcess cp
         return out
         else parseItHelp cp isEnd out

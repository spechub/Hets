{- |
Module      : $Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ProveUtils offer a list of commands for preparing the theory for
proving
-}

module PGIP.ProveUtils
       ( cParseScript
       ) where

import Logic.Prover
import GUI.GenericATPState
import List

-- reads an integer from a string
rInt :: String -> Int
rInt = read

-- finds out time limit value from the script (if any)
getTLimit :: String -> Maybe Int
getTLimit str
 = let ln =  find (\x -> let w = head $ words x
                         in (w == "time_limit")) $ lines str
   in case ln of
       Nothing -> Nothing
       Just sm -> Just $ rInt $ head $ tail $ words sm

-- takes out information about time limit
extractTLimit :: String -> [String]
extractTLimit str
  = filter (\x -> let w = head $ words x
                  in (w /= "time_limit")) $ lines str

-- | Parses the tactic script to extract time limit and other commands
cParseScript :: Int -> [String] -> Tactic_script -> ATPTactic_script
cParseScript tLimit extOpts (Tactic_script ts)
 = let time_limit = case getTLimit ts of
                     Nothing -> tLimit
                     Just t -> t
       opts = case ts of
               [] -> extOpts
               _  -> extractTLimit ts
   in ATPTactic_script {
           ts_timeLimit = time_limit,
           ts_extraOpts = opts
           }



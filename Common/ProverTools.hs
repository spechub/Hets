{- |
Module      :  $Header$
Description :  Check for availability of provers
Copyright   :  (c) Dminik Luecke, and Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

check for provers
-}

module Common.ProverTools
    where

import Common.Utils

import System.Directory
import System.IO.Unsafe

-- ^ Checks if a Prover Binary exists and is executable
-- ^ in an unsafe manner
unsafeProverCheck :: String -- ^ prover Name
                  -> String -- ^ Environment Variable
                  -> a
                  -> [a]
unsafeProverCheck name env a = unsafePerformIO $
                               check4Prover name env a

-- ^ Checks if a Prover Binary exists and is executable
check4Prover :: String -- ^ prover Name
             -> String -- ^ Environment Variable
             -> a
             -> IO [a]
check4Prover name env a =
    do
      pPath <- getEnvDef env ""
      let path = splitOn ':' pPath
      exIT <- mapM (\x -> doesFileExist $ x ++ "/" ++ name) path
      let exI = zip path exIT
          ex = filter (\(_,y) -> y == True) exI
      case ex of
        [] ->
            do
              return []
        _  ->
            do
              let pt = map (\(x,_) -> x) ex
              execI <- mapM (\x -> getPermissions $ x ++ "/" ++ name) pt
              let exec = or $ map (executable) execI
              if (exec)
               then
                   do
                     return [a]
               else
                   do
                     return [a]

-- ^ Checks if a Prover Binary exists in an unsafe manner
unsafeFileCheck :: String -- ^ prover Name
                -> String -- ^ Environment Variable
                -> a
                -> [a]
unsafeFileCheck name env a = unsafePerformIO $ check4File name env a

-- ^ Checks if a Prover Binary exists
check4File ::   String -- ^ prover Name
             -> String -- ^ Environment Variable
             -> a
             -> IO [a]
check4File name env a =
    do
      pPath <- getEnvDef env ""
      let path = splitOn ':' pPath
      exIT <- mapM (\x -> doesFileExist $ x ++ "/" ++ name) path
      let ex = or exIT
      if ex
       then
           return [a]
       else
           return []

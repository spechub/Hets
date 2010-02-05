
module LF.Shellout where

import System.IO
import System.Process

import Data.List (isPrefixOf)

import Common.Doc
import Common.DocUtils (Pretty(..))
import Common.Utils

twelfPath :: String
twelfPath = "check-some"
twelfArgs :: [String]
twelfArgs = ["-omdoc", "."]
twelfHetsPath :: String
twelfHetsPath = ""

-- | runs @twelf@ in an interactive subprocess
runTwelf :: IO (Handle, Handle, Handle, ProcessHandle)
runTwelf = runInteractiveProcess twelfPath twelfArgs Nothing Nothing


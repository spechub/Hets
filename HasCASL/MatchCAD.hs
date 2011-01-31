{- |
Module      :  $Header$
Description :  MatchCAD program
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

Program for matching to HasCASL exported CAD designs against design patterns
-}


import System.Environment
import System.Console.GetOpt

import HasCASL.InteractiveTests
import Data.Bits
import Data.Maybe
import Data.List



main :: IO ()
main = do
  args <- getArgs
  case processArgs args of
    Left msg -> putStrLn $ "Design Matching: " ++ msg ++ "\n\n" ++ dmUsage
    Right st ->
        matchDesign (lib st) (spec st) (pattern st) $ design st

------------------------- Input Arguments -------------------------

processArgs :: [String] -> Either String ProgSettings
processArgs args =
    let (flags, noopts, unrecopts, errs) = getOpt' (ReturnInOrder PFLib) options args
        msgl = checkFlags flags
        f str (l, s) = if null l then str else str ++ "\n" ++ s ++ unlines l
        msg = foldl f ""
              [ (noopts, "non-handled extra arguments encountered ")
              , (unrecopts, "unrecognized flags encountered ")
              , (errs, "")
              , (msgl, "")
              ]
    in if null msg then Right $ getSettings flags else Left msg

dmUsage :: String
dmUsage = let header = "Usage: matchcad [OPTION...] [file]"
          in usageInfo header options

{- | 'options' describes all available options and is used to generate usage
information -}
options :: [OptDescr ProgFlag]
 -- Option [Char] [String] (ArgDescr a) String
options = map f $
          [ ( "lib", "Path to the hets file", ReqArg PFLib "FILE")
          , ( "spec"
            , "Name of specification importing both, the pattern and the design specification"
            , ReqArg PFSpec "SPECNAME")
          , ( "pattern", "Name of the pattern specification"
            , ReqArg PFPattern "SPECNAME")
          , ( "design", "Name of the design specification"
            , ReqArg PFDesign "SPECNAME")
          , ( "verbosity"
            , "A value from 0=quiet to 4=print out all information during processing"
            , OptArg (PFVerbosity . read . fromMaybe "4")  "0-4")
          , ( "quiet", "Equal to -v0", NoArg PFQuiet)
          ] where
    f (fs, descr, arg) = Option [head fs] [fs] arg descr

checkFlags :: [ProgFlag] -> [String]
checkFlags = g . mapAccumL f (0::Int) where
    f i (PFLib _) = (setBit i 0, ())
    f i (PFSpec _) = (setBit i 1, ())
    f i (PFPattern _) = (setBit i 2, ())
    f i (PFDesign _) = (setBit i 3, ())
    f i _ = (i, ())
    g (i, _) = mapMaybe (h i) [ (0, "lib")
                              , (1, "spec")
                              , (2, "pattern")
                              , (3, "design") ]
    h i (j, s)
      | testBit i j = Nothing
      | otherwise = Just $ s ++ " argument is missing"

data ProgSettings =
    ProgSettings
    { lib :: String
    , spec :: String
    , pattern :: String
    , design :: String
    , verbosity :: Int }


defaultSettings :: ProgSettings
defaultSettings = ProgSettings
                  { lib = error "uninitialized settings"
                  , spec = error "uninitialized settings"
                  , pattern = error "uninitialized settings"
                  , design = error "uninitialized settings"
                  , verbosity = 4 }

data ProgFlag =
    PFLib String
        | PFSpec String
        | PFPattern String
        | PFDesign String
        | PFVerbosity Int
        | PFQuiet

makeSettings :: ProgSettings -> ProgFlag -> ProgSettings
makeSettings settings flg =
    case flg of
      PFLib s -> settings { lib = s }
      PFSpec s -> settings { spec = s }
      PFPattern s -> settings { pattern = s }
      PFDesign s -> settings { design = s }
      PFVerbosity i -> settings { verbosity = i }
      PFQuiet -> settings { verbosity = 0 }
      
getSettings :: [ProgFlag] -> ProgSettings
getSettings = foldl makeSettings defaultSettings


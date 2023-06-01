{- |
Module      :  ./Maude/Shellout.hs
Description :  Maude Development Graphs
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

-}

module Maude.Shellout (
    runMaude,
    basicAnalysis,
    findSpec,
    getAllSpec,
    getErrors,
    maudePutStrLn
) where

import System.FilePath
import System.IO
import System.Process
import System.Timeout

import Maude.AS_Maude

import Maude.Sign (Sign, inlineSign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

import Data.List (isPrefixOf)

import Common.Doc
import Common.DocUtils ()
import Common.Utils

import qualified Control.Monad.Fail as Fail

maudePath :: String
maudePath = "maude"
maudeArgs :: [String]
maudeArgs = ["-interactive", "-no-banner", "-no-advise"]
maudeHetsPath :: String
maudeHetsPath = "hets.prj"

-- | runs @maude@ in an interactive subprocess
runMaude :: IO (String, Handle, Handle, Handle, ProcessHandle)
runMaude = do
  ml <- getEnvDef "MAUDE_LIB" ""
  hml <- getEnvDef "HETS_MAUDE_LIB" "Maude"
  if null ml then error "environment variable MAUDE_LIB is not set" else do
    (hIn, hOut, hErr, procH) <-
        runInteractiveProcess maudePath maudeArgs Nothing Nothing
    return ("in " ++ hml </> maudeHetsPath, hIn, hOut, hErr, procH)

maudePutStrLn :: Handle -> String -> IO ()
maudePutStrLn hIn str = do
  hPutStrLn hIn str
  hFlush hIn

{- | performs the basic analysis, extracting the signature and the sentences
of the given Maude text, that can use the signature accumulated thus far. -}
basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText mt) = do
    (inString, hIn, hOut, _, _) <- runMaude
    maudePutStrLn hIn inString
    let sigStr = show $ parens
          $ vcat [text "mod FROM-HETS is", inlineSign sign, text mt
                 , text "endm"]
    maudePutStrLn hIn sigStr
    specOut <- hGetContents hOut
    hClose hIn
    let spStr = findSpec specOut
    case readMaybe spStr of
      Just sp -> return $ convertSpec sp
      Nothing ->
          Fail.fail $ "cannot interpret the following maude output:\n" ++ spStr
          ++ "\ncreated for:\n" ++ sigStr
          ++ "\nmaude return:\n" ++ specOut

-- | extracts the signature and the sentences from a specification
convertSpec :: Spec -> (Sign, [Sentence])
convertSpec (SpecMod spec) = (Sign.fromSpec spec, Sen.fromSpec spec)
convertSpec _ = (Sign.empty, [])

-- | extracts the string corresponding to a specification
findSpec :: String -> String
findSpec = let
        findSpecBeg = dropWhile $ not . isPrefixOf "Spec"
        findSpecEnd = takeWhile $ not . isPrefixOf "@#$endHetsSpec$#@"
        filterNil = filter $ (/=) '\NUL'
    in filterNil . unlines . findSpecEnd . findSpecBeg . lines

-- | extracts the Haskell representation of a Maude module or view
getAllSpec :: Handle -> String -> Bool -> IO String
getAllSpec hOut s False = do
    ready <- hWaitForInput hOut 2000
    if ready
        then do  -- 5 secs per line
            ms <- timeout 5000000 $ hGetLine hOut
            case ms of
              Nothing -> return s
              Just ss -> getAllSpec hOut (s ++ "\n" ++ ss) (finalSpec ss)
        else do
            handle <- hShow hOut
            error $ "No spec available on handle: " ++ handle
getAllSpec _ s True = return s

getErrors :: Handle -> IO (Bool, String)
getErrors hErr = do
  ss <- hGetContents hErr
  return (null ss, ss)

-- | end of the Haskell representation of a Maude module or view
finalSpec :: String -> Bool
finalSpec "@#$endHetsSpec$#@" = True
finalSpec _ = False

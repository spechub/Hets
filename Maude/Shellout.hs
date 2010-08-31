{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}

module Maude.Shellout (
    runMaude,
    basicAnalysis,
    findSpec,
    getAllOutput,
    getAllSpec,
    getErrors
) where

import System.IO
import System.Process

import Maude.AS_Maude

import Maude.Sign (Sign,inlineSign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

import Data.List (isPrefixOf)

import Common.Doc
import Common.DocUtils ()
import Common.Utils

maudePath :: String
maudePath = "maude"
maudeArgs :: [String]
maudeArgs = ["-interactive", "-no-banner", "-no-advise"]
maudeHetsPath :: String
maudeHetsPath = "Maude/hets.prj"

-- | runs @maude@ in an interactive subprocess
runMaude :: IO (Handle, Handle, Handle, ProcessHandle)
runMaude = runInteractiveProcess maudePath maudeArgs Nothing Nothing

-- | performs the basic analysis, extracting the signature and the sentences
-- of the given Maude text, that can use the signature accumulated thus far
basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText mt) = do
    (hIn, hOut, _, _) <- runMaude
    hPutStrLn hIn $ unwords ["in", maudeHetsPath]
    let sigStr = show $ parens
          $ vcat [text "mod FROM-HETS is", inlineSign sign, text mt, text "endm"]
    hPutStrLn hIn sigStr
    hFlush hIn
    specOut <- hGetContents hOut
    hClose hIn
    let spStr = findSpec specOut
    case readMaybe spStr of
      Just sp -> return $ convertSpec sp
      Nothing ->
          fail $ "cannot interpret the following maude output:\n" ++ spStr
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
        filterNil   = filter $ (/=) '\NUL'
    in filterNil . unlines . findSpecEnd . findSpecBeg . lines

-- | extracts a Maude module or view
getAllOutput :: Handle -> String -> Bool -> IO String
getAllOutput hOut s False = do
    ready <- hWaitForInput hOut 500
    if ready
        then do
            ss <- hGetLine hOut
            getAllOutput hOut (s ++ "\n" ++ ss) (final ss)
        else do
            handle <- hShow hOut
            error $ "No output available on handle: " ++ handle
getAllOutput _ s True = return $ prepare s

-- | extracts the Haskell representation of a Maude module or view
getAllSpec :: Handle -> String -> Bool -> IO String
getAllSpec hOut s False = do
    ready <- hWaitForInput hOut 500
    if ready
        then do
            ss <- hGetLine hOut
            getAllSpec hOut (s ++ "\n" ++ ss) (finalSpec ss)
        else do
            handle <- hShow hOut
            error $ "No spec available on handle: " ++ handle
getAllSpec _ s True = return s

getErrors :: Handle -> IO (Bool, String)
getErrors hErr = do
               ready <- hWaitForInput hErr 500
               if ready
                   then do
                         ss <- hGetLine hErr
                         return (ok (drop 9 ss), ss)
                   else return (True, "")

ok :: String -> Bool
ok ('<' : _) = True
ok _ = False

-- | possible ends of a Maude module or view
final :: String -> Bool
final "endfm" = True
final "endm" = True
final "endth" = True
final "endfth" = True
final "endv" = True
final _ = False

-- | end of the Haskell representation of a Maude module or view
finalSpec :: String -> Bool
finalSpec "@#$endHetsSpec$#@" = True
finalSpec _ = False

-- | drops the header and adds the parens for Full Maude
prepare :: String -> String
prepare s = "(" ++ drop 8 s ++ ")"

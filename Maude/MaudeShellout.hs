
module Maude.MaudeShellout (basicAnalysis) where

import System.IO
import System.Process

import Maude.AS_Maude
import Maude.Printing (printSign)

import Maude.Sign (Sign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

import Data.List (isPrefixOf)


maudePath :: String
maudePath = "/Applications/maude-darwin/maude.intelDarwin"
maudeCmd :: String
maudeCmd = unwords [maudePath, "-interactive", "-no-banner"]
maudeHetsPath :: String
maudeHetsPath = "/Users/adrian/Hets/Maude/hets.prj"


basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText text) = do
    (hIn, hOut, _, _) <- runInteractiveCommand maudeCmd
    hPutStrLn hIn $ unwords ["in", maudeHetsPath]
    let printedSign = printSign (Sign.sorts sign) (Sign.subsorts sign) (Sign.ops sign)
    hPutStrLn hIn $ unwords ["(fmod FROM-HETS is", printedSign, text, "endfm)"]
    hClose hIn
    specOut <- hGetContents hOut
    return $ convertSpec $ read $ findSpec specOut

convertSpec :: Spec -> (Sign, [Sentence])
convertSpec (SpecMod spec) = (Sign.fromSpec spec, Sen.getSentences spec)
convertSpec _ = (Sign.empty, [])

findSpec :: String -> String
findSpec = filterNil . unlines . findSpecEnd . findSpecBeg . lines
    where
        findSpecBeg = dropWhile $ not . isPrefixOf "Spec"
        findSpecEnd = takeWhile $ not . isPrefixOf "@#$endHetsSpec$#@"
        filterNil   = filter $ (/=) '\NUL'

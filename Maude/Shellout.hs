
module Maude.Shellout (basicAnalysis, findSpec) where

import System.IO
import System.Process

import Maude.AS_Maude

import Maude.Sign (Sign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

import Data.List (isPrefixOf)

import Common.Doc
import Common.DocUtils (Pretty(..))


maudePath :: String
maudePath = "/Applications/maude-darwin/maude.intelDarwin"
maudeCmd :: String
maudeCmd = unwords [maudePath, "-interactive", "-no-banner"]
maudeHetsPath :: String
maudeHetsPath = "/Users/adrian/Hets/Maude/hets.prj"


basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText mt) = do
    (hIn, hOut, _, _) <- runInteractiveCommand maudeCmd
    hPutStrLn hIn $ unwords ["in", maudeHetsPath]
    let printedSign = parens $ vsep [text "fmod FROM-HETS is", pretty sign, text mt, text "endfm"]
    hPutStrLn hIn $ show printedSign
    hClose hIn
    specOut <- hGetContents hOut
    return $ convertSpec $ read $ findSpec specOut

convertSpec :: Spec -> (Sign, [Sentence])
convertSpec (SpecMod spec) = (Sign.fromSpec spec, Sen.fromSpec spec)
convertSpec _ = (Sign.empty, [])

findSpec :: String -> String
findSpec = let
        findSpecBeg = dropWhile $ not . isPrefixOf "Spec"
        findSpecEnd = takeWhile $ not . isPrefixOf "@#$endHetsSpec$#@"
        filterNil   = filter $ (/=) '\NUL'
    in filterNil . unlines . findSpecEnd . findSpecBeg . lines

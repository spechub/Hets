
module Maude.MaudeShellout (basicAnalysis) where

import System.IO
import System.Process

import Maude.AS_Maude
import Maude.Sign
import Maude.Printing
import Maude.Sentence


maude_cmd :: String
maude_cmd = "/Applications/maude-darwin/maude.intelDarwin -interactive -no-banner"

-- wait_threshold = 100


basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText mt) = do
    (hIn, hOut, _, _) <- runInteractiveCommand maude_cmd -- (hIn, hOut, hErr, hProcess)
    hPutStrLn hIn "in /Users/adrian/Hets/Maude/hets.prj"
    hPutStrLn hIn ("(fmod A is " ++ (printSign (sorts sign) (subsorts sign) (ops sign))
                   ++ mt ++ " endfm)")
    hClose hIn
    sOutput <- hGetContents hOut
    let stringSpec = getSpec sOutput
    let spec = read stringSpec :: Spec
    basicAnalysisAux spec

basicAnalysisAux :: Spec -> IO (Sign, [Sentence])
basicAnalysisAux (SpecMod sp_module) = do
    let nsign = fromSpec sp_module
    let sen = getSentences sp_module
    return (nsign, sen)
basicAnalysisAux _ = return (empty, [])


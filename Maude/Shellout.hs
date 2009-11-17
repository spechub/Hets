
module Maude.Shellout (basicAnalysis, findSpec, getAllOutput, getAllSpec) where

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
maudePath = "maude"
maudeCmd :: String
maudeCmd = unwords [maudePath, "-interactive", "-no-banner", "-no-advise"]
maudeHetsPath :: String
maudeHetsPath = "Maude/hets.prj"

-- | performs the basic analysis, extracting the signature and the sentences
-- of the given Maude text, that can use the signature accumulated thus far
basicAnalysis :: Sign -> MaudeText -> IO (Sign, [Sentence])
basicAnalysis sign (MaudeText mt) = do
    (hIn, hOut, _, _) <- runInteractiveCommand maudeCmd
    hPutStrLn hIn $ unwords ["in", maudeHetsPath]
    let printedSign = parens $ vcat [text "mod FROM-HETS is", pretty sign, text mt, text "endm"]
    hPutStrLn hIn $ show printedSign
    specOut <- hGetContents hOut
    hClose hIn
    return $ convertSpec $ read $ findSpec specOut

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
                 ss <- hGetLine hOut
                 getAllOutput hOut (s ++ "\n" ++ ss) (final ss)
getAllOutput _ s True = return $ prepare s

-- | extracts the Haskell representation of a Maude module or view
getAllSpec :: Handle -> String -> Bool -> IO String
getAllSpec hOut s False = do
                 ss <- hGetLine hOut
                 getAllSpec hOut (s ++ "\n" ++ ss) (finalSpec ss)
getAllSpec _ s True = return s

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
prepare s = "(" ++ (drop 8 s) ++ ")"

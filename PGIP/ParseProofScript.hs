{- |
Module      :  $Header$
Description :  parse a heterogeneous proof script and return it as pgip-xml
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

import Interfaces.Command

import CMDL.ParseProofScript
import CMDL.DataTypes

import PGIP.XMLstate

import Common.Utils

import Text.XML.Light as XML

import Data.Either
import Data.List

import System.Environment

parseContent :: FilePath -> String -> Either String [LitCommand]
parseContent fp str = let
  l = number $ lines str
  (es, rs) = partitionEithers $ map
    (\ (s, i) -> parseSingleLine fp i s) l
  in if null es then Right rs else
     Left $ unlines es

whiteSpaceElems :: String -> [Element]
whiteSpaceElems str = if null str then [] else [unode "whitespace" str]

litString :: LitCommand -> String
litString c = word (commandWW c)
  ++ maybe "" (\ a -> leading a ++ word a) (argumentWW c)

closeTheory :: Bool -> [Element]
closeTheory isOpen = [unode "closetheory" () | isOpen]

xmlLitCmds :: String -> Bool -> [LitCommand] -> [Element]
xmlLitCmds trailer isOpen ls = case ls of
  [] -> closeTheory isOpen ++ whiteSpaceElems trailer
  h : r ->
    let wsp = trailer ++ leading (commandWW h)
        wspes = whiteSpaceElems wsp
    in case cmdDescription $ command h of
    SelectCmd LibFile _ ->
      wspes ++ closeTheory isOpen ++
      [unode "opentheory" $ litString h]
      ++ xmlLitCmds (trailing h ++ "\n") True r
    GroupCmd _ -> xmlLitCmds (wsp ++ "\n") isOpen r
    CommentCmd _ -> xmlLitCmds (wsp ++ litString h ++ "\n") isOpen r
    _ -> wspes ++ [unode "proofstep" $ litString h]
         ++ xmlLitCmds (trailing h ++ "\n") isOpen r

parseHPF :: Bool -> FilePath -> IO ()
parseHPF normal fp = do
  str <- readFile fp
  putStrLn $ case parseContent fp str of
    Left err -> showElement $ genErrorResponse True err
    Right rs -> (if normal then showElement . genNormalResponse "" else
                     intercalate "\n" . map (showElement . unode "pgip"))
      $ xmlLitCmds "" False rs

-- with an argument "-" the output can be standard input for hets -I -x
main :: IO ()
main = do
  args <- getArgs
  let (opts, files) = partition (isPrefixOf "-") args
  mapM_ (parseHPF $ null opts) files

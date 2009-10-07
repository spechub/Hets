{- |
Module      :  $Header$
Description :  parse a heterogeneous proof script and return it as pgip-xml
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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

parseHPF :: FilePath -> IO ()
parseHPF fp = do
  str <- readFile fp
  putStrLn $ showElement $ case parseContent fp str of
    Left err -> genErrorResponse True err
    Right rs -> genNormalResponse "" $ xmlLitCmds "" False rs

main :: IO ()
main = getArgs >>= mapM_ parseHPF

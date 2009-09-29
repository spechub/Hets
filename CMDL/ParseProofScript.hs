{- |
Module      :  $Header$
Description :  parse a heterogeneous proof script and return it as pgip-xml
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Main where

import Interfaces.Command

import CMDL.DataTypes
import CMDL.Commands

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos (initialPos)

import Text.XML.Light as XML

import Common.Utils

import Data.Char
import Data.Either
import Data.List

import System.Environment

data WhiteWord = WhiteWord
  { leading :: String -- ^ leading white space
  , word :: String }

data LitCommand = LitCommand
  { commandWW :: WhiteWord
  , argumentWW :: Maybe WhiteWord
  , trailing :: String -- ^ trailing white space
  , command :: Command }

parseLine :: [Command] -> FilePath -> Int -> Parser LitCommand
parseLine cl fp i = do
  setPosition $ setSourceLine (initialPos fp) i
  s1 <- many space
  (eof >> return LitCommand
      { commandWW = WhiteWord "" ""
      , argumentWW = Nothing
      , trailing = s1
      , command = GroupCmd [] }) <|> do
    (cs, cm) <- choice (map (\ (c, sl) -> do
      s <- try $ parseCommand sl
      return (s, c)) $ (GlobCmd ProveCurrent, ["prove-all"])
        : map (\ c -> (c, words $ cmdNameStr c)) cl)
      <|> do
        h <- char '#'
        r <- many anyChar
        return (h : r, CommentCmd r)
    s2 <- many space
    (eof >> return LitCommand
        { commandWW = WhiteWord s1 cs
        , argumentWW = Nothing
        , trailing = s2
        , command = cm }) <|> do
      (arg, s3) <- parseArgument
      return LitCommand
        { commandWW = WhiteWord s1 cs
        , argumentWW = Just $ WhiteWord s2 arg
        , trailing = s3
        , command = setInputStr arg cm }

parseArgument :: Parser (String, String)
parseArgument = do
  arg <- many1 (satisfy $ not . isSpace)
  sp <- many space
  (eof >> return (arg, sp)) <|> do
    (rargs, s) <- parseArgument
    return (arg ++ sp ++ rargs, s)

parseCommand :: [String] -> Parser String
parseCommand cmd = case cmd of
   [] -> fail ""
   [c] -> string c
   c : r -> do
     string c
     s <- many1 space
     t <- parseCommand r
     return $ c ++ s ++ t

parseContent :: FilePath -> String -> Either String [LitCommand]
parseContent fp str = let
  l = number $ lines str
  (es, rs) = partitionEithers $ map (\ (s, i) ->
     parse (parseLine (map cmdDescription getCommands) fp i) fp s) l
  in if null es then Right rs else
     Left $ unlines $ map show es

whiteSpaceElems :: String -> [Element]
whiteSpaceElems str = if null str then [] else [unode "whitespace" str]

litString :: LitCommand -> String
litString c = word (commandWW c)
  ++ maybe "" (\ a -> leading a ++ word a) (argumentWW c)

closeTheory :: Bool -> [Element]
closeTheory isOpen = if isOpen then [unode "closetheory" ()] else []

xmlLitCmds :: String -> Bool -> [LitCommand] -> [Element]
xmlLitCmds trailer isOpen ls = case ls of
  [] -> closeTheory isOpen ++ whiteSpaceElems trailer
  h : r ->
    let wsp = trailer ++ leading (commandWW h)
        wspes = whiteSpaceElems wsp
    in case command h of
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
  case parseContent fp str of
    Left err -> putStrLn err
    Right rs -> putStrLn $ unlines $ map showElement
                $ xmlLitCmds "" False rs

main :: IO ()
main = getArgs >>= mapM_ parseHPF



{- |
Module      :  $Header$
Description :  parse a heterogeneous proof script
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module CMDL.ParseProofScript where

import Interfaces.Command

import CMDL.DataTypes
import CMDL.Commands

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos (initialPos)

import Data.Char

data WhiteWord = WhiteWord
  { leading :: String -- ^ leading white space
  , word :: String }

data LitCommand = LitCommand
  { commandWW :: WhiteWord
  , argumentWW :: Maybe WhiteWord
  , trailing :: String -- ^ trailing white space
  , command :: CmdlCmdDescription }

parseLine :: [CmdlCmdDescription] -> FilePath -> Int -> Parser LitCommand
parseLine cl fp i = do
  setPosition $ setSourceLine (initialPos fp) i
  s1 <- many space
  (eof >> return LitCommand
      { commandWW = WhiteWord "" ""
      , argumentWW = Nothing
      , trailing = s1
      , command = cmdlIgnoreFunc "" }) <|> do
    (cs, cm) <- choice (map (\ (c, sl) -> do
      s <- try $ parseCommand sl
      return (s, c)) $ (proveAll, ["prove-all"])
        : map (\ c -> (c, words $ cmdNameStr $ cmdDescription c)) cl)
      <|> do
        h <- char '#'
        r <- many anyChar
        return (h : r, cmdlIgnoreFunc r)
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
        , command = cm
            { cmdDescription = setInputStr arg $ cmdDescription cm } }

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

parseSingleLine :: FilePath -> Int -> String -> Either String LitCommand
parseSingleLine fp i str =
  case parse (parseLine getCommands fp i) fp str of
    Left e -> Left $ show e
    Right r -> Right r

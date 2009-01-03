{- |
Module      :  $Header$
Description :  test some parsers (and printers)
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

test some parsers (and printers)
-}

module Common.RunParsers (exec, StringParser, toStringParser, fromAParser)
    where

import Common.Lexer((<<), parseString)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Common.AnnoParser
import Common.AnnoState
import Common.DocUtils
import Common.GlobalAnnotations
import Common.AnalyseAnnos(addGlobalAnnos)
import Common.Result
import System.Environment

type StringParser = GlobalAnnos -> AParser () String

fromAParser :: Pretty a => AParser () a -> StringParser
fromAParser p ga = fmap (\ a -> showGlobalDoc ga a "") p

toStringParser :: Pretty a => (GlobalAnnos -> AParser () a) -> StringParser
toStringParser p ga = fmap (\ a -> showGlobalDoc ga a "") $ p ga

exec :: [(String, StringParser)] -> [(String, StringParser)] -> IO ()
exec lps fps = do
  l <- getArgs
  case l of
   [] -> parseSpec emptyGlobalAnnos $ snd $ head $ fps
   opt : tl -> do
    let lps' = filter (\(s, _) -> s == opt) lps
        fps' = filter (\(s, _) -> s == opt) fps
    ga <- case tl of
     [] -> return emptyGlobalAnnos
     annoFile : _ -> do
        str <- readFile annoFile
        maybe (error "run parser") return $ maybeResult
          $ addGlobalAnnos emptyGlobalAnnos
          $ parseString annotations str
          -- should not fail
          -- but may return empty annos
    case (lps', fps') of
      ([], []) -> do
        putStrLn ("unknown option: " ++ opt)
        p <- getProgName
        putStrLn $ "Usage: " ++ p ++ " [OPTIONS] <Annotations> < infile"
        putStrLn "where OPTIONS is one of:"
        putStrLn $ unwords $ map fst lps ++ map fst fps
      ([], (_, hd) : _) -> parseSpec ga hd
      ((_, hd) : _, _) -> checkLines ga hd

checkLines :: GlobalAnnos -> StringParser -> IO ()
checkLines ga p =
  getContents >>= putStr . unlines . scanLines ga p 1 . lines

scanLines :: GlobalAnnos -> StringParser -> Line -> [String] -> [String]
scanLines ga p n inp = case inp of
  [] -> []
  x : l -> parseLine ga p x n : scanLines ga p (n + 1) l

parseLine :: GlobalAnnos -> StringParser -> String -> Line -> String
parseLine ga p line n =
    let pos = setSourceLine (initialPos "") n
        parser = do
          setPosition pos
          i <- p ga
          eof
          return i
        in showParse $ runParser parser (emptyAnnos ()) "" line

parseSpec :: GlobalAnnos -> StringParser -> IO ()
parseSpec ga p =
  getContents >>= putStrLn . showParse
    . runParser (p ga << eof) (emptyAnnos ()) ""

showParse :: Either ParseError String -> String
showParse e = case e of
  Left err -> "parse error at " ++ showErr err ++ "\n"
  Right x -> x

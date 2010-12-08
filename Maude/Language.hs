{- |
Module      :  $Header$
Description :  Parsing the Maude Language
Copyright   :  (c) Martin Kuehl, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Parsing the Maude language with Haskell and "Parsec".
-}

module Maude.Language (
    -- * Types

    -- ** The Named Spec type
    NamedSpec (..),
    -- ** Parser Result types
    ParseResult,
    RawResult,

    -- * Parsers for Maude

    -- ** The Abstract Parser
    maudeParser,
    -- ** The Raw Parser
    parseFromFile,
    -- ** The Refined Parser
    parse,
) where

import Text.ParserCombinators.Parsec hiding (parseFromFile, parse)
import qualified Text.ParserCombinators.Parsec as Parsec (parseFromFile)

import Maude.Parse

import Common.Parsec ((<:>), (<<), single)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Char (isSpace)
import Data.List (nub)
import Data.Maybe (fromJust, isNothing)

-- * Types

-- ** The Named Spec type
data NamedSpec = ModName String     -- ^ A Module or Theory
               | ViewName String    -- ^ A View
               deriving (Show, Read, Eq)

-- ** Parser Result types

-- | Parsed Result for a module tree
type ParseResult = [NamedSpec]
-- | Parsed Result for a single declaration
type RawResult = Maybe (Either FilePath NamedSpec)
-- | Intermediate Result during module tree recursion
type RecResult = (Set FilePath, ParseResult)

-- * Generic Parser combinators

-- | Run the argument but return 'Nothing'
ignore :: (Monad m) => m a -> m (Maybe b)
ignore parser = parser >> return Nothing

-- | Wrap the result of a successful parse
succeed :: (Monad m) => a -> m (Maybe (Either b a))
succeed = return . Just . Right

-- | A list of characters Maude considers special
specialChars :: String
specialChars = "()[]{},"

opLetter :: CharParser () Char
opLetter = let
  special = char '`' >>= flip option (oneOf specialChars)
  in special <|> satisfy (\ c -> not $ isSpace c || elem c specialChars)

identifier :: CharParser () String
identifier = lexeme $ anyChar <:> many opLetter

reserved :: String -> CharParser () ()
reserved n = lexeme $ try (string n >> notFollowedBy opLetter)

lexeme :: CharParser () a -> CharParser () a
lexeme = (<< whiteSpace)

whiteSpace :: CharParser () ()
whiteSpace = skipMany $ single space <|> blockComment <|> lineComment

-- * Helper functions for parsing Maude

-- | Match any of the arguments as 'reserved' words
anyReserved :: [String] -> CharParser () ()
anyReserved = choice . map reserved

-- | Match any 'identifier' or 'operator'
something :: CharParser () String
something = identifier
-- Identifiers and operators are identical currently.

-- | Match a dot-terminated statement
statement :: CharParser () [String]
statement = lexeme $ manyTill something $ char '.'

-- | Match the rest of a line
line :: CharParser () String
line = lexeme $ many $ noneOf "\n"

-- * Parsers for Maude source code and components

-- | Parse Maude source code
toplevel :: CharParser () [RawResult]
toplevel = let
    components = [systemCmd, otherCmd, debuggerCmd, modul, theory, view]
    in whiteSpace >> many1 (choice components)

-- | Parse a system command
systemCmd :: CharParser () RawResult
systemCmd = let
    otherSym = anyReserved
               ["quit", "eof", "popd", "pwd", "cd", "push", "ls"]
    other = ignore $ otherSym >> line
    loadSym = anyReserved ["in", "load"]
    load = loadSym >> fmap (Just . Left) line
    in load <|> other

-- | Parse a command
otherCmd :: CharParser () RawResult
otherCmd = let
    symbol = anyReserved
             ["select", "parse", "debug", "reduce", "rewrite",
              "frewrite", "erewrite", "match", "xmatch", "search",
              "continue", "loop", "trace", "print", "break", "show",
              "do", "set"]
    in ignore $ symbol >> statement

-- | Parse a debugger command.
debuggerCmd :: CharParser () RawResult
debuggerCmd = let symbol = anyReserved ["resume", "abort", "step", "where"]
              in ignore $ symbol >> statement

-- | Parse a Maude module
modul :: CharParser () RawResult
modul = let
    modul' start stop = do
        reserved start
        name <- identifier
        manyTill something $ reserved "is"
        manyTill statement $ reserved stop
        succeed $ ModName name
    in modul' "fmod" "endfm"
    <|> modul' "mod" "endm"

-- | Parse a Maude theory
theory :: CharParser () RawResult
theory = let
    theory' start stop = do
        reserved start
        name <- identifier
        reserved "is"
        manyTill statement $ reserved stop
        succeed $ ModName name
    in theory' "fth" "endfth"
    <|> theory' "th" "endth"

-- | Parse a Maude view
view :: CharParser () RawResult
view = do
    reserved "view"
    name <- identifier
    manyTill statement $ reserved "endv"
    succeed $ ViewName name

-- * Parsers for Maude source files

-- | Parse Maude source code
maudeParser :: CharParser () [RawResult]
maudeParser = toplevel

-- | Parse a single Maude source file
parseFromFile :: FilePath ->
                 IO (Either ParseError [RawResult])
parseFromFile = Parsec.parseFromFile maudeParser

-- | Parse a Maude source file and the collect the results
parseFileAndCollect :: FilePath -> RecResult ->
                       IO (Either ParseError RecResult)
parseFileAndCollect path results@(done, syms)
    | Set.member path done = return $ Right results
    | otherwise = do
        parsed <- parseFromFile path
        case parsed of
            Left err -> return $ Left err
            Right res -> collectParseResults res (Set.insert path done, syms)

-- | Collect the results from parsing a Maude source file
collectParseResults :: [RawResult] -> RecResult ->
                       IO (Either ParseError RecResult)
collectParseResults list results@(done, syms)
    | null list = return $ Right results
    | isNothing $ head list = collectParseResults (tail list) results
    | otherwise = case fromJust $ head list of
        Right symb -> collectParseResults (tail list) (done, symb : syms)
        Left path -> do
            parsed <- parseFileAndCollect path results
            case parsed of
                Right res -> collectParseResults (tail list) res
                Left err -> return $ Left err

-- | Parse a Maude source tree
parse :: FilePath ->
         IO (Either ParseError ParseResult)
parse path = do
    parsed <- parseFileAndCollect path (Set.empty, [])
    case parsed of
        Left err -> return $ Left err
        Right res -> return $ Right $ nub $ reverse $ snd res

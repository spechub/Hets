{- |
Module      :  $Header$
Description :  Parsing the Maude Language
Copyright   :  (c) Martin Kuehl, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import Text.ParserCombinators.Parsec (ParseError, CharParser)
import Text.ParserCombinators.Parsec.Prim ((<|>))
import Text.ParserCombinators.Parsec.Char
import Text.ParserCombinators.Parsec.Combinator
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Text.ParserCombinators.Parsec.Language as Language
import qualified Text.ParserCombinators.Parsec as Parsec (parseFromFile)

import Data.Set (Set)
import qualified Data.Set as Set

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

-- | Run the argument but return unit
void :: (Monad m) => m a -> m ()
void parser = parser >> return ()

-- | Run the argument but return 'Nothing'
ignore :: (Monad m) => m a -> m (Maybe b)
ignore parser = parser >> return Nothing

-- | Wrap the result of a successful parse
succeed :: (Monad m) => a -> m (Maybe (Either b a))
succeed = return . Just . Right

-- * Helper functions for Parsec.Language

-- | Run the argument after ensuring we aren't looking at whitespace
nonSpace :: CharParser () a -> CharParser () a
nonSpace parser = notFollowedBy space >> parser

-- | Match a literal backquote character
backquote :: CharParser () Char
backquote = char '`'

-- | A list of characters Maude considers "special"
specialChars :: String
specialChars = "()[]{},"

-- * Maude in Parsec.Language

-- | The Maude 'Parsec.Language.LanguageDef'
maudeLanguageDef :: Language.LanguageDef ()
maudeLanguageDef = Language.emptyDef {
    -- TODO: Get comments right.
    Language.commentStart   = "***(",
    Language.commentEnd     = ")",
    Language.commentLine    = "---", -- also: "***"
    Language.nestedComments = True,
    Language.caseSensitive  = True,
    Language.identStart     = Token.opStart maudeLanguageDef,
    Language.identLetter    = Token.opLetter maudeLanguageDef,
    Language.opStart        = anyChar,
    Language.opLetter       = let
        special = backquote >>= flip option (oneOf specialChars)
        other = noneOf specialChars
        in nonSpace $ special <|> other
}

-- | The Maude 'Parsec.Token.TokenParser'
maudeTokenParser :: Token.TokenParser ()
maudeTokenParser = Token.makeTokenParser maudeLanguageDef

-- Yes, this is how Parsec.Language is _supposed_ to be used...

identifier :: CharParser () String
identifier = Token.identifier maudeTokenParser
reserved :: String -> CharParser () ()
reserved = Token.reserved maudeTokenParser
lexeme :: CharParser () a -> CharParser () a
lexeme = Token.lexeme maudeTokenParser
whiteSpace :: CharParser () ()
whiteSpace = Token.whiteSpace maudeTokenParser
dot :: CharParser () String
dot = Token.dot maudeTokenParser

-- * Helper functions for parsing Maude

-- | Match any of the arguments as 'reserved' words
anyReserved :: [String] -> CharParser () ()
anyReserved = choice . map reserved

-- | Match any 'identifier' or 'operator'
something :: CharParser () String
something = identifier
-- Identifiers and operators are identical currently.

-- | Match a 'dot'-terminated statement
statement :: CharParser () [String]
statement = manyTill something dot

-- | Match the rest of a line
line :: CharParser () String
line = manyTill anyChar $ eof <|> void (lexeme newline)

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
    load = do loadSym; name <- line; return $ Just $ Left name
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
    in  modul' "fmod" "endfm"
    <|> modul' "mod"  "endm"

-- | Parse a Maude theory
theory :: CharParser () RawResult
theory = let
    theory' start stop = do
        reserved start
        name <- identifier
        reserved "is"
        manyTill statement $ reserved stop
        succeed $ ModName name
    in  theory' "fth" "endfth"
    <|> theory' "th"  "endth"

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
            Left  err -> return $ Left err
            Right res -> collectParseResults res ((Set.insert path done), syms)

-- | Collect the results from parsing a Maude source file
collectParseResults :: [RawResult] -> RecResult ->
                       IO (Either ParseError RecResult)
collectParseResults list results@(done, syms)
    | null list = return $ Right results
    | isNothing $ head list = collectParseResults (tail list) results
    | otherwise = case fromJust $ head list of
        Right symb -> collectParseResults (tail list) (done, (symb:syms))
        Left  path -> do
            parsed <- parseFileAndCollect path results
            case parsed of
                Right res -> collectParseResults (tail list) res
                Left  err -> return $ Left err

-- | Parse a Maude source tree
parse :: FilePath ->
         IO (Either ParseError ParseResult)
parse path = do
    parsed <- parseFileAndCollect path (Set.empty, [])
    case parsed of
        Left  err -> return $ Left err
        Right res -> return $ Right $ nub $ reverse $ snd res

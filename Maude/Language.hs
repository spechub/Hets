module Maude.Language (
    parseMaudeICantThinkOfAnyName
) where


import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Text.ParserCombinators.Parsec.Language as Language

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as Fold

import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)


--- The types we use for our parsers

-- TODO: Replace String with the right data types

type Parsed = Either ParseError
type Symbol = String
-- Result of a single component
type TempResult = Maybe (Either FilePath Symbol)
type TempParser = CharParser () TempResult
type TempListParser = CharParser () [TempResult]
-- Result of a single module
type ModResult = (Set FilePath, Set Symbol)
type ModParser = CharParser () ModResult
-- Result during module tree recursion
type RecResult = (Set FilePath, Set FilePath, Set Symbol)
-- Result for a module tree
type MaudeResult = Set Symbol


--- Generic parser combinators

-- | Run the given |parser| but return unit
void :: (Monad m) => m a -> m ()
void parser = parser >> return ()

-- | Run the given |parser| but return Nothing
ignore :: (Monad m) => m a -> m (Maybe b)
ignore parser = parser >> return Nothing


--- A few helpers we need for Parsec.Language

-- | Run the given |parser| after ensuring we aren't looking at whitespace
nonSpace :: CharParser () a -> CharParser () a
nonSpace parser = notFollowedBy space >> parser

-- | Match a literal backquote character
backquote :: CharParser () Char
backquote = char '`'

-- | A list of characters Maude considers "special"
specialChars :: String
specialChars = "()[]{},"


--- The Parsec.Language definition of Maude

maudeLanguageDef :: Language.LanguageDef ()
maudeLanguageDef = Language.emptyDef {
    -- TODO: Get comments right.
    Language.commentStart    = "***(",
    Language.commentEnd      = ")",
    Language.commentLine     = "---", -- also: "***"
    Language.nestedComments  = True,
    Language.caseSensitive   = True,
    Language.identStart      = Token.opStart maudeLanguageDef,
    Language.identLetter     = Token.opLetter maudeLanguageDef,
    Language.opStart         = anyChar,
    Language.opLetter        = nonSpace $ (backquote >>= flip option (oneOf specialChars)) <|> noneOf specialChars
}

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


--- A few more helpers for parsing Maude

-- | Match any of the given strings as a |reserved| word
anyReserved :: [String] -> CharParser () ()
anyReserved = choice . map reserved

-- | Match any identifier or operator
-- Identifiers and operators are identical currently.
something :: CharParser () String
something = identifier

-- | Match a |dot|-terminated statement
statement :: CharParser () [String]
statement = manyTill something dot

-- | Match the rest of a line
-- TODO: Figure out how the characters are interpreted by Maude.
line :: CharParser () String
line = manyTill anyChar $ eof <|> void (lexeme newline)


--- Parsers for Maude source code and components

-- | Parse Maude source code
toplevel :: TempListParser
toplevel = let components = [systemCmd, otherCmd, debuggerCmd, modul, theory, view]
    in whiteSpace >> many1 (choice components)


-- | Parse a system command
systemCmd :: TempParser
systemCmd = let
        otherSym = anyReserved ["quit", "eof", "popd", "pwd", "cd", "push", "ls"]
        other = ignore $ otherSym >> line
        loadSym = anyReserved ["in", "load"]
        load = do
            loadSym
            name <- line
            return $ Just $ Left name
    in load <|> other

-- | Parse a command
otherCmd :: TempParser
otherCmd = let symbol = anyReserved ["select", "parse", "debug", "reduce", "rewrite", "frewrite", "erewrite", "match", "xmatch", "search", "continue", "loop", "trace", "print", "break", "show", "do", "set"]
    in ignore $ symbol >> statement

-- | Parse a debugger command.
debuggerCmd :: TempParser
debuggerCmd = let symbol = anyReserved ["resume", "abort", "step", "where"]
    in ignore $ symbol >> statement


-- | Parse a Maude module
modul :: TempParser
modul = let
        modul' start stop = do
            reserved start
            name <- identifier
            manyTill something $ reserved "is"
            manyTill statement $ reserved stop
            return $ Just $ Right name
    in  modul' "fmod" "endfm"
    <|> modul' "mod"  "endm"

-- | Parse a Maude theory
theory :: TempParser
theory = let
        theory' start stop = do
            reserved start
            name <- identifier
            reserved "is"
            manyTill statement $ reserved stop
            return $ Just $ Right name
    in  theory' "fth" "endfth"
    <|> theory' "th"  "endth"

-- | Parse a Maude view
view :: TempParser
view = do
    reserved "view"
    name <- identifier
    manyTill statement $ reserved "endv"
    return $ Just $ Right name


--- Parsers for Maude source files

-- | Parse Maude source code and clean up the results
parseMaude :: ModParser
parseMaude = do
    results <- toplevel
    let (files, symbols) = partitionEithers $ catMaybes results
    return (Set.fromList files, Set.fromList symbols)

-- | Parse a single Maude source file
parseMaudeFromFile :: FilePath -> IO (Parsed ModResult)
parseMaudeFromFile = parseFromFile parseMaude

-- | Parse a single Maude source file and insert the results into the given Sets
parseMaudeFile :: FilePath -> Parsed RecResult -> IO (Parsed RecResult)
parseMaudeFile path result = case result of
    Left _ -> return result
    Right (todo, done, syms) -> if Set.member path done
        then return result
        else do
            parsed <- parseMaudeFromFile path
            case parsed of
                Left err -> return $ Left err
                Right (files, symbols) -> let
                        todo' = Set.union todo files
                        done' = Set.insert path done
                        syms' = Set.union syms symbols
                    in return $ Right (todo', done', syms')

-- | Parse a set of Maude source files recursively
parseMaudeFold :: Set FilePath -> Set FilePath -> Set String -> IO (Parsed MaudeResult)
parseMaudeFold todo done syms = do
    let initial = Right (Set.empty, done, syms)
    parsed <- Fold.foldrM parseMaudeFile initial todo
    case parsed of
        Left err -> return $ Left err
        Right (todo', done', syms') -> if Set.null todo'
            then return $ Right syms'
            else parseMaudeFold todo' done' syms'

-- TODO: Give this function a real name
parseMaudeICantThinkOfAnyName :: FilePath -> IO (Parsed MaudeResult)
parseMaudeICantThinkOfAnyName path = parseMaudeFold (Set.singleton path) Set.empty Set.empty

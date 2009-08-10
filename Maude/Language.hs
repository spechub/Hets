module Maude.Language (
    parseMaudeFromFile
) where


import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Text.ParserCombinators.Parsec.Language as Language

-- import Data.Set (Set)
-- import qualified Data.Set as Set

import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)


--- The types we use for our parsers

type MaudeResult = ([String], [String])
type MaudeParser = CharParser () MaudeResult
type MaudeTempResult = Maybe (Either String String)
type MaudeTempParser = CharParser () MaudeTempResult
type MaudeListParser = CharParser () [MaudeTempResult]


--- General parser combinators

-- | Run the given |parser| but return Nothing 
ignore :: (Monad m) => m a -> m (Maybe b)
ignore parser = parser >> return Nothing


--- A few helpers we need for Parsec.Language

-- | Run a parser after ensuring we aren't looking at whitespace
nonSpace :: CharParser () a -> CharParser () a
nonSpace = (>>) $ notFollowedBy space

-- | Match a literal backquote character
backquote :: CharParser () Char
backquote = char '`'

-- | A list of characters Maude considers "special"
specialChars :: String
specialChars = "()[]{},"


--- The Parsec.Language definition of Maude

maudeDef :: Language.LanguageDef ()
maudeDef = Language.emptyDef {
    -- TODO: Get comments right.
    Language.commentStart    = "***(",
    Language.commentEnd      = ")",
    Language.commentLine     = "---", -- also: "***"
    Language.nestedComments  = True,
    Language.caseSensitive   = True,
    Language.identStart      = Token.opStart maudeDef,
    Language.identLetter     = Token.opLetter maudeDef,
    Language.opStart         = anyChar,
    Language.opLetter        = nonSpace $ (backquote >>= (flip option) (oneOf specialChars)) <|> noneOf specialChars
}

maude :: Token.TokenParser ()
maude = Token.makeTokenParser maudeDef


--- Yes, this is how Parsec.Language is _supposed_ to be used...

identifier :: CharParser () String
identifier = Token.identifier maude
reserved :: String -> CharParser () ()
reserved = Token.reserved maude
lexeme :: CharParser () a -> CharParser () a
lexeme = Token.lexeme maude
whiteSpace :: CharParser () ()
whiteSpace = Token.whiteSpace maude
dot :: CharParser () String
dot = Token.dot maude


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
line = manyTill anyChar $ lexeme newline


--- Parsers for Maude source code and components

-- | Parse Maude source code
maudeTop :: MaudeListParser
maudeTop = let components = [systemCmd, otherCmd, debuggerCmd, modul, theory, view]
    in whiteSpace >> many1 (choice components)


-- | Parse a system command
systemCmd :: MaudeTempParser
systemCmd = load <|> other where
    load = do
        loadSym
        name <- line
        return $ Just $ Left name
    loadSym = anyReserved ["in", "load"]
    other = ignore $ otherSym >> line
    otherSym = anyReserved ["quit", "eof", "popd", "pwd", "cd", "push", "ls"]

-- | Parse a command
otherCmd :: MaudeTempParser
otherCmd = let symbol = anyReserved ["select", "parse", "debug", "reduce", "rewrite", "frewrite", "erewrite", "match", "xmatch", "search", "continue", "loop", "trace", "print", "break", "show", "do", "set"]
    in ignore $ symbol >> statement

-- | Parse a debugger command.
debuggerCmd :: MaudeTempParser
debuggerCmd = let symbol = anyReserved ["resume", "abort", "step", "where"]
    in ignore $ symbol >> statement


-- | Parse a Maude module
modul :: MaudeTempParser
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
theory :: MaudeTempParser
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
view :: MaudeTempParser
view = do
    reserved "view"
    name <- identifier
    manyTill statement $ reserved "endv"
    return $ Just $ Right name


--- Parsers for Maude source files

{-
    We construct a tuple of lists of String, the first list containing FilePaths and the second containing symbols.
    TODO: Recursively parse the files for the extracted paths and add all their symbols to our list.
    TODO: Make sure the result list doesn't contain duplicates
    TODO: Make sure we don't parse files twice (mutual recursion)
    TODO: Replace String with the right data types
-}

-- | Parse Maude source code and clean up the results
parseMaude :: MaudeParser
parseMaude = do
    results <- maudeTop
    return $ partitionEithers $ catMaybes results

parseMaudeFiles :: [FilePath] -> [String] -> IO (Either ParseError MaudeResult)
parseMaudeFiles paths symbols = case paths of
    [] -> return $ Right ([], symbols)
    this:rest -> do
        result <- parseFromFile parseMaude this
        case result of
            Left _ -> return result
            Right (fs, ss) -> parseMaudeFiles (rest ++ fs) (symbols ++ ss)

-- | Parse a Maude source file
parseMaudeFromFile :: FilePath -> IO (Either ParseError MaudeResult)
parseMaudeFromFile path = parseMaudeFiles [path] []
    -- parseFromFile parseMaude

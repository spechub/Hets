module Maude.Language (
    NamedSpec (..),
    maudeParser,
    parseFromFile,
    parse
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


--- The types we use for our parsers

data NamedSpec = ModName String
               | ViewName String
    deriving (Show, Read, Eq)

type Parsed = Either ParseError
-- Result of a single component
type TempResult = Maybe (Either FilePath NamedSpec)
type TempParser = CharParser () TempResult
type TempListResult = [TempResult]
type TempListParser = CharParser () TempListResult
-- Result during module tree recursion
type RecResult = (Set FilePath, MaudeResult)
-- Result for a module tree
type MaudeResult = [NamedSpec]


--- Generic parser combinators

-- | Run the given |parser| but return unit
void :: (Monad m) => m a -> m ()
void parser = parser >> return ()

-- | Run the given |parser| but return Nothing
ignore :: (Monad m) => m a -> m (Maybe b)
ignore parser = parser >> return Nothing

-- | Wrap the result of a successful parse
succeed :: (Monad m) => a -> m (Maybe (Either b a))
succeed = return . Just . Right

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
toplevel = let
        components = [systemCmd, otherCmd, debuggerCmd, modul, theory, view]
    in whiteSpace >> many1 (choice components)


-- | Parse a system command
systemCmd :: TempParser
systemCmd = let
        otherSym = anyReserved
            ["quit", "eof", "popd", "pwd", "cd", "push", "ls"]
        other = ignore $ otherSym >> line
        loadSym = anyReserved ["in", "load"]
        load = do loadSym; name <- line; return $ Just $ Left name
    in load <|> other

-- | Parse a command
otherCmd :: TempParser
otherCmd = let
        symbol = anyReserved
            ["select", "parse", "debug", "reduce", "rewrite",
             "frewrite", "erewrite", "match", "xmatch", "search",
             "continue", "loop", "trace", "print", "break", "show",
             "do", "set"]
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
            succeed $ ModName name
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
            succeed $ ModName name
    in  theory' "fth" "endfth"
    <|> theory' "th"  "endth"

-- | Parse a Maude view
view :: TempParser
view = do
    reserved "view"
    name <- identifier
    manyTill statement $ reserved "endv"
    succeed $ ViewName name


--- Parsers for Maude source files

-- | Parse Maude source code and clean up the results
maudeParser :: TempListParser
maudeParser = toplevel

-- | Parse a single Maude source file
parseFromFile :: FilePath -> IO (Parsed TempListResult)
parseFromFile = Parsec.parseFromFile maudeParser

-- | Parse a Maude source file and the collect the results
parseFileAndCollect :: FilePath -> RecResult -> IO (Parsed RecResult)
parseFileAndCollect path results@(done, syms)
    | Set.member path done = return $ Right results
    | otherwise = do
        parsed <- parseFromFile path
        case parsed of
            Left  err -> return $ Left err
            Right res -> collectParseResults res ((Set.insert path done), syms)

-- | Collect the results from parsing a Maude source file
collectParseResults :: TempListResult -> RecResult -> IO (Parsed RecResult)
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
parse :: FilePath -> IO (Parsed MaudeResult)
parse path = do
    parsed <- parseFileAndCollect path (Set.empty, [])
    case parsed of
        Left  err -> return $ Left err
        Right res -> return $ Right $ nub $ reverse $ snd res

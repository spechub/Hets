module Maude.Language (
    parseMaudeFromFile
) where


import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Text.ParserCombinators.Parsec.Language as Language

import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)


type MaudeResult = ([String], [String])
type MaudeParser = CharParser () MaudeResult
type MaudeTempResult = Maybe (Either String String)
type MaudeTempParser = CharParser () MaudeTempResult
type MaudeListParser = CharParser () [MaudeTempResult]


nonSpace :: GenParser Char st a -> GenParser Char st a
nonSpace = (>>) $ notFollowedBy space


specialChars :: String
specialChars = "()[]{},"

backquote :: CharParser st Char
backquote = char '`'

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

identifier = Token.identifier maude
reserved = Token.reserved maude
lexeme = Token.lexeme maude
whiteSpace = Token.whiteSpace maude
dot = Token.dot maude

{-
    We construct a tuple of lists of String, the first list containing FilePaths and the second containing symbols.
    TODO: Recursively parse the files for the extracted paths and add all their symbols to our list.
-}

parseMaudeFromFile :: FilePath -> IO (Either ParseError MaudeResult)
parseMaudeFromFile = parseFromFile parseMaude

parseMaude :: MaudeParser
parseMaude = do
    results <- maudeTop
    return $ partitionEithers $ catMaybes results


anyReserved = choice . map reserved
something = identifier
statement = manyTill something dot
-- TODO: Figure out how the characters are interpreted by Maude.
line = manyTill anyChar $ lexeme newline
ignore parser = parser >> return Nothing


maudeTop :: MaudeListParser
maudeTop = whiteSpace >> many1 (choice [systemCmd, otherCmd, debuggerCmd, modul, theory, view])


systemCmd :: MaudeTempParser
systemCmd = load <|> other where
    load = do
        loadSym
        name <- line
        return $ Just $ Left name
    loadSym = anyReserved ["in", "load"]
    other = ignore $ otherSym >> line
    otherSym = anyReserved ["quit", "eof", "popd", "pwd", "cd", "push", "ls"]

otherCmd :: MaudeTempParser
otherCmd = ignore $ otherSym >> statement where
    otherSym = anyReserved ["select", "parse", "debug", "reduce", "rewrite", "frewrite", "erewrite", "match", "xmatch", "search", "continue", "loop", "trace", "print", "break", "show", "do", "set"]

debuggerCmd :: MaudeTempParser
debuggerCmd = ignore $ debuggerSym >> statement where
    debuggerSym = anyReserved ["resume", "abort", "step", "where"]


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

view :: MaudeTempParser
view = do
    reserved "view"
    name <- identifier
    manyTill statement $ reserved "endv"
    return $ Just $ Right name

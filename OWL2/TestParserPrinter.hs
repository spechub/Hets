module OWL2.TestParserPrinter where

import OWL2.AS
import OWL2.PrintMS
import qualified OWL2.ParseMS as PMS
import qualified OWL2.ParseAS as PAS


import Prelude hiding (lookup)


import Common.AnnoParser (newlineOrEof)
import Common.Parsec
import Common.Lexer (getNumber, value)
import Common.Doc (text, empty)
import Common.DocUtils
import qualified Common.GlobalAnnotations as GA (PrefixMap)

import Text.ParserCombinators.Parsec

import Data.Char
import Data.Map (union, toList, fromList, lookup)
import Data.Maybe
import Data.List (sort, isSuffixOf)
import System.Directory (getDirectoryContents, getCurrentDirectory)
import Debug.Trace

-- -- parses all file in given directories and displays whether parsing was successful
-- runAllTestsInDir :: FilePath -> IO ()
-- runAllTestsInDir d = do
--     files <- getDirectoryContents d
--     sequence (runTest <$> filter (isSuffixOf ".ofn") (sort files))
--     return ()
--     where 
--         runTest f = do
--             content <- readFile (d ++ "/" ++ f)
--             let emptyOntDoc = OntologyDocument [] 
--                     (Ontology Nothing Nothing [] [] [])
--                 resParse1Either = parse (parseOntologyDocument mempty) f content
--                 resParse1 = either (const emptyOntDoc) id resParse1Either
--                 -- resParse1NoPrefix = removePrefix resParse1 
--                 resPrint = pretty resParse1
--                 resParse2Either  = parse (parseOntologyDocument mempty)
--                     f (show resPrint)
--                 resParse2 = either (const emptyOntDoc) id resParse2Either
--                 result = resParse1 == resParse2
--                 resString = if result then "✅ Success" else "❌ Failed"
--             putStr resString
--             putStrLn $ ": " ++ d ++ "/" ++ f

-- -- tests parsing on all OWL2/tests/**/*.ofn files
-- pta :: IO ()
-- pta = forget $ sequence (runAllTestsInDir <$> dirs)
--     where dirs = [
--             "./OWL2/tests",
--             "./OWL2/tests/1",
--             "./OWL2/tests/2",
--             "./OWL2/tests/3",
--             "./OWL2/tests/4",
--             "./OWL2/tests/5",
--             "./OWL2/tests/6",
--             "./OWL2/tests/7",
--             "./OWL2/tests/8",
--             "./OWL2/tests/9"]

-- parses the test.ofn file in the current directory and prints the result
-- pt :: IO ()
-- pt = do
--     content <- readFile "./test.ofn"
--     parseTest (parseOntologyDocument mempty) content
--     return ()

-- dTest :: IO ()
-- dTest = do 
--     content <- readFile "./OWL2/tests/myTest.ofn"
--     let fErr = "./OWL2/tests/myError.txt"
--         fOut = "./OWL2/tests/myOutput.txt"
--         fOutParser = "./OWL2/tests/myOutputParser.txt"
--         emptyOntDoc = OntologyDocument [] 
--             (Ontology Nothing Nothing [] [] [])
--         resParse1Either = parse (parseOntologyDocument mempty) fErr content
--         resParse1 = either (const emptyOntDoc) id resParse1Either
--         -- resParse1NoPrefix = removePrefix resParse1 
--         resPrint = pretty resParse1
--         resParse2Either  = parse (parseOntologyDocument mempty)
--             fErr (show resPrint)
--         resParse2 = either (const emptyOntDoc) id resParse2Either
--         result = resParse1 == resParse2

--     -- putStrLn $ "Parser\n" ++ "========================="
--     -- putStrLn $ (show resParse1) ++ "\n"
--     -- putStrLn $ "Printer\n" ++ "========================="
--     -- putStrLn $ (show resPrint) ++ "\n"
--     putStrLn $ "Are Parser and Printer consistent?\n"
--         ++ "========================="
--     putStrLn $ show result
--     writeFile fOut $ show resPrint
--     writeFile fOutParser $ show resParse1
--     return ()

removePrefix :: OntologyDocument -> OntologyDocument
removePrefix (OntologyDocument pds ont) =
    OntologyDocument [] ont

testMS :: IO ()
testMS = do
    content <- readFile "./OWL2/tests/myTest.omn"
    let fErr = "./OWL2/tests/myError.txt"
        fOut = "./OWL2/tests/myOutput.txt"
        fOutParser = "./OWL2/tests/myOutputParser.txt"
        emptyOntDoc = OntologyDocument [] 
            (Ontology Nothing Nothing [] [] [])
        resParse1Either = parse (PMS.parseOntologyDocument mempty) fErr content
        resParse1 = either (const emptyOntDoc) id resParse1Either
        resPrint = pretty resParse1
    writeFile fOut $ show resPrint
    writeFile fOutParser $ show resParse1
    return ()

testAS :: IO ()
testAS = do
    content <- readFile "./OWL2/tests/myTest.ofn"
    let fErr = "./OWL2/tests/myError.txt"
        fOut = "./OWL2/tests/myOutput.txt"
        fOutParser = "./OWL2/tests/myOutputParser.txt"
        emptyOntDoc = OntologyDocument [] 
            (Ontology Nothing Nothing [] [] [])
        resParse1Either = parse (PAS.parseOntologyDocument mempty) fErr content
        resParse1 = either (const emptyOntDoc) id resParse1Either
        resPrint = pretty resParse1
    writeFile fOut $ show resPrint
    writeFile fOutParser $ show resParse1
    return ()

testOneMS :: IO ()
testOneMS = do
    content <- readFile "./OWL2/tests/myTest.omn"
    let fErr = "./OWL2/tests/myError.txt"
        fOut = "./OWL2/tests/myOutput.txt"
        fOutParser = "./OWL2/tests/myOutputParser.txt"
        emptyOntDoc = OntologyDocument [] 
            (Ontology Nothing Nothing [] [] [])
        resParse1Either = parse (PMS.parseOntologyDocument mempty) fErr content
        resParse1 = either (const emptyOntDoc) id resParse1Either
        resPrint = pretty resParse1
        resParse2Either  = parse (PMS.parseOntologyDocument mempty)
            fErr (show resPrint)
        resParse2 = either (const emptyOntDoc) id resParse2Either
        result = resParse1 == resParse2
    writeFile fOutParser $ show resParse1
    writeFile fOut $ show resPrint
    -- putStrLn $ "Are MS printer and MS parser consistent? : " ++ show result
    return ()

testMSParser :: IO ()
testMSParser = do
    content <- readFile "./OWL2/tests/myTest.omn"
    let fErr = "./OWL2/tests/myError.txt"
        fOutParser = "./OWL2/tests/myOutputParser.txt"
        emptyOntDoc = OntologyDocument [] 
            (Ontology Nothing Nothing [] [] [])
        resParse1Either = parse (PMS.parseOntologyDocument mempty) fErr content
        resParse1 = either (const emptyOntDoc) id resParse1Either
    writeFile fOutParser $ show resParse1
    return ()
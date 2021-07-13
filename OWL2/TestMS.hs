module OWL2.TestMS where

import System.IO
import System.Directory
import Data.List (sort,isSuffixOf, (\\))
import Data.Map(empty)
import Control.Monad

import Common.Parsec
import Text.ParserCombinators.Parsec

import OWL2.ParseMS

-- parses all file in given directories and displays whether parsing was successful
runAllTestsInDir :: FilePath -> IO (Int, Int, Int)
runAllTestsInDir d = do
    contents <- getDirectoryContents d
    let files = filter (isSuffixOf ".omn") (sort contents)
    excluded <- filterM (\f -> getFileSize (d ++ "/" ++ f) >>= return . (>= 10*1024*1024)) files
    nums <- sequence (runTest <$> (files \\ excluded))
    return (sum nums, length files, length excluded)
    where 
        runTest f = do
            let path = d ++ "/" ++ f            
            content <- readFile path
            putStrLn $ "Parsing '" ++ path ++ "'"
            let res = parse (parseOntologyDocument empty) f content
            putStrLn $ either (\e -> "  ❌ Failed: " ++ show e) (const "  ✅ Success") res
            return $ either (const 0) (const 1) res

-- tests parsing on all OWL2/tests/**/*.ofn files
pta :: IO ()
pta = do 
  stats <- sequence (runAllTestsInDir <$> dirs)
  let successful = sum $ map (\(a, _, _) -> a) stats
  let skipped = sum $ map (\(_, _, a) -> a) stats
  let total = sum $ map (\(_, a, _) -> a) stats
  let ratio =  successful * 100 `div` total * 100 `div` 100
  putStrLn $ show successful ++ "/" ++ show total ++ " (" ++ show ratio ++"%) tests passed. " ++ show skipped ++ " tests skipped."
    where dirs = [
            "./OWL2/tests",
            "./OWL2/tests/1",
            "./OWL2/tests/2",
            "./OWL2/tests/3",
            "./OWL2/tests/4",
            "./OWL2/tests/5",
            "./OWL2/tests/6",
            "./OWL2/tests/7",
            "./OWL2/tests/8",
            "./OWL2/tests/9",
            "../bioportal"]

-- parses the test.ofn file in the current directory and prints the result
pt :: IO ()
pt = do
    content <- readFile "./test.omn"
    parseTest (parseOntologyDocument empty) content
    return ()
    
-- parses the test.ofn file in the current directory and prints the result
ps :: IO ()
ps = do
    content <- readFile "./test.omn"
    let res = parse (parseOntologyDocument empty) "" content
    putStrLn $ either (\e -> "❌ Failed:\n" ++ show e) (const "✅ Success") res

    return ()

-- getFileSize :: FilePath -> IO (Integer)
-- getFileSize path = handle (return 0) $ bracket (openFile path ReadMode) (hClose) hFileSize

main :: IO ()
main = pta


{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett and Markus Roggenbach and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Test case wrapper for CspCASL specs and fragments.

This is a standalone `main' wrapper for CspCASL-related tests
performed locally to the CspCASL codebase.  It's probably only of
interest to the CspCASL maintainers.

The "test" directory contains (negative & positive) test cases.  Each
test case is identified by a *.testcase file, with the following
structure:

  - The first line is the name of the file containing the input source
    to use for this test case (also in the test directory).

  - The second line identifies which parser is being tested (eg
    "Process", "Core-CspCASL").

  - The third line identifies whether this is a positive (++) or
    negative (--) test case.

  - If it's a positive test case, the remaining lines contain the
    expected output of the pretty printer.

  - If it's a negative test case, the remaining lines contain
    information about the expected error.  (Not yet
    implemented/defined.)

-}

module Main where

import Directory
import System.Environment
import System.IO
import Text.ParserCombinators.Parsec

import Common.AnnoState (emptyAnnos)
import Common.DocUtils

import CspCASL.Parse_CspCASL
import CspCASL.Parse_CspCASL_Process()
import CspCASL.Print_CspCASL()

data TestCase = TestCase String String String String

instance Show TestCase where show = showTC

showTC :: TestCase -> String
showTC (TestCase src parser sense _)
    = "TestCase " ++ src ++ "(" ++ parser ++ ")" ++ sense

main :: IO ()
main = do contents <- readAllTests "test"
          print (show contents)

-- Given path to directory containing test cases, return list of test
-- cases.
readAllTests :: FilePath -> IO [TestCase]
readAllTests path = do tests <- listTestCases path
                       mapM readOneTestCase tests

-- List every file in the test directory ending with '.testcase'
listTestCases :: FilePath -> IO [FilePath]
listTestCases path = let
    endswith :: String -> String -> Bool
    endswith subject target = drop (length subject - length target) subject == target
    isTestCase :: String -> Bool
    isTestCase f = endswith f ".testcase"
    in do contents <- getDirectoryContents path
          let testcases = (map (\x -> path ++ "/" ++ x) (filter isTestCase contents))
          return testcases

-- Given the path to a .testcase file, return TestCase described therein.
readOneTestCase :: FilePath -> IO TestCase
readOneTestCase tc = do hdl <- openFile tc ReadMode
                        contents <- hGetContents hdl
                        return (interpret contents)

interpret :: String -> TestCase
interpret s = TestCase source parser sense output
    where ls = lines s
          source = head ls
          parser = head (tail ls)
          sense = head (tail (tail ls))
          output = unlines (tail (tail (tail ls)))












prettyCspCASLFromFile :: FilePath -> IO ()
prettyCspCASLFromFile fname
  = do input <- readFile fname
       putStr ("Input:\n" ++ input ++ "Pretty print:\n")
       case (runParser basicCspCaslSpec (emptyAnnos ()) fname input) of
           Left err -> do putStr "parse error at "
                          print err
           Right x  -> do putStrLn $ showDoc x ""
                          -- print x -- print parse tree

-- parseFiles: Given a list of filenames, parse each file in turn.

parseFiles :: [String] -> IO()
parseFiles arg = case arg of
    []            -> do putStr "" -- kinda stupid
    (path:others) -> do prettyCspCASLFromFile path
			parseFiles others

testOne :: IO()
testOne
    = do case (runParser dataDefn (emptyAnnos ()) "" "SKIP") of
           Left err -> do putStr "parse error at "
                          print err
           Right x  -> do putStrLn $ showDoc x ""
                          print x










oldmain :: IO ()
oldmain = do filenames <- getArgs
             parseFiles filenames
             --testOne

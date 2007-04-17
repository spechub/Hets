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
    information about the expected error.

-}

module Main where

import Directory
import List
import System.IO
import Text.ParserCombinators.Parsec

import Common.AnnoState (emptyAnnos)
import Common.DocUtils

import CspCASL.Parse_CspCASL(basicCspCaslSpec)
import CspCASL.Parse_CspCASL_Process(csp_casl_process)
import CspCASL.Print_CspCASL()

-- |Tests may be positive or negative.  A positive test is one where
-- we expect the parser to succeed.  A negative test is one where we
-- expect it to fail.  For positive tests, we test that the result of
-- unparsing the parse tree matches the original source input.  For
-- negative tests, we test that the error messages produced are as we
-- would expect.
data TestSense = Positive | Negative
                 deriving (Eq, Ord, Show)

data TestCase = TestCase {
      -- | @src_file@ - name of file containing source code of test case
      src_file :: String,
      -- | @parser@ - name of parser to apply to that source
      parser :: String,
      -- | @sense@ - sense of test (positive or negative)
      sense :: TestSense,
      -- | @expected@ - expected output of test
      expected :: String,
      -- | @src@ - actual source contained in src_file
      src :: String
} deriving (Eq, Ord)
instance Show TestCase where
  show a = (show (sense a)) ++ "Test " ++ (src_file a) ++ "(" ++ (parser a) ++ ")"

-- Tests can have the following outcomes: they can pass, in that the
-- outcome is as we would expect; or they can fail, in that the
-- outcome is not as we would expect.  For a positive test, the
-- expected outcome is an unparsed parse tree; for a negative test,
-- the expected outcome is the error string.

data TestOutcome = TestPass TestCase
                 | TestFail TestCase String



main :: IO ()
main = do contents <- readAllTests "test"
          clart (map performTest (sort contents))
          --print (show contents)

clart :: [TestOutcome] -> IO ()
clart [] = do putStr ""
clart ((TestPass tc):xs) = do putStr ((src_file tc) ++ " passed\n")
                              clart xs
clart ((TestFail tc o):xs) = do putStr ((src_file tc) ++ " failed\n")
                                putStr (o ++ "\nvs\n" ++ (expected tc) ++ "\n--\n")
                                clart xs

trim      :: [Char] -> [Char]
trim      = applyTwice (reverse . trim1) 
    where  trim1 = dropWhile (`elem` delim) 
           delim    = [' ', '\t', '\n', '\r']
           applyTwice f = f . f

--groove :: TestCase -> String
--groove tc = (src_file tc) ++ "\n" ++ (parseTestCase tc)
--    where outcome = performTest tc

--onesie :: String -> IO ()
--onesie s = print s


performTest :: TestCase -> TestOutcome
performTest tc = if (trim actual) == (trim (expected tc))
                 then TestPass tc
                 else TestFail tc actual
    where actual = parseTestCase tc

-- | Run a test case, parsing the specified file and returning a
-- string containing either the unparsed parse tree (ie more source),
-- or the text of the error message.
parseTestCase :: TestCase -> String
-- This implementation is horrible; there must be a better way than
-- this copy-and-paste case distinction.  For every parser we want to
-- be able to test, we'll have to add an essentially copied-and-pasted
-- case - yuk!  Unfortunately either I don't know a better way or I
-- don't know that I know one.
parseTestCase t =
    let es = emptyAnnos ()
        fn = src_file t
        s = src t
    in case (parser t) of
         "CoreCspCASL" -> case (runParser basicCspCaslSpec es fn s) of
                            Left err -> show err
                            Right x  -> showDoc x ""
         "Process" -> case (runParser csp_casl_process es fn s) of
                        Left err -> show err
                        Right x  -> showDoc x ""
         _ -> error "Parser name"




-- Everything else is the yucky I/O stuff for reading the test cases.



-- |Given a path to a directory containing test cases, return a list
-- of test case values.
readAllTests :: FilePath -> IO [TestCase]
readAllTests path = do tests <- listTestCases path
                       mapM (readOneTestCase path) tests

-- |List every file in the test directory ending with '.testcase'
listTestCases :: FilePath -> IO [FilePath]
listTestCases path = let
    endswith subject target = drop (length subject - length target) subject == target
    isTestCase f = endswith f ".testcase"
    in do contents <- getDirectoryContents path
          let testcases = (map (\x -> path ++ "/" ++ x) (filter isTestCase contents))
          return testcases

-- |Given the path to a .testcase file, return TestCase value
-- described therein.
readOneTestCase :: FilePath -> FilePath -> IO TestCase
readOneTestCase dir tc = do hdl <- openFile tc ReadMode
                            contents <- hGetContents hdl
                            let (a, b, c, d) = (interpret contents)
                            hdl_s <- openFile (dir ++ "/" ++ a) ReadMode
                            e <- hGetContents hdl_s
                            return TestCase { src_file = a, parser = b, sense = c,
                                              expected = d, src = e }

-- |Given the textual content of a .testcase file, split it into
-- strings representing the various parts of the test case.
interpret :: String -> (String, String, TestSense, String)
interpret s = (head ls,
               head (tail ls),
               interpretSense (head (tail (tail ls))),
               unlines (tail (tail (tail ls))))
    where ls = lines s

-- |Interpret a test case sense (++ or --, positive or negative)
interpretSense :: String -> TestSense
interpretSense s = case s of
                     "++" ->  Positive
                     "--" -> Negative
                     _ -> error "Test sense"

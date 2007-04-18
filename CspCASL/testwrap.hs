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

-- | Test sense: do we expect parse success or failure?  What is the
-- nature of the expected output?
data TestSense
    -- | expect successful parse; check unparsed result.
    = Positive
    -- | expect parse failure; check error message.
    | Negative
                 deriving (Eq, Ord)
instance Show TestSense where
  show Positive = "++"
  show Negative = "--"

-- | Test case details: where is source, what is it, which parser, etc.
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
  show a = (src_file a) ++ " (" ++ (show (sense a)) ++ (parser a) ++ ")"

data TestOutcome = TestPass TestCase
                 | TestFail TestCase String

main :: IO ()
main = do contents <- readAllTests "test"
          printResults (map performTest (sort contents))

printResults :: [TestOutcome] -> IO ()
printResults [] = do putStr ""
printResults ((TestPass tc):xs) = do putStr ((show tc) ++ " passed\n")
                                     printResults xs
printResults ((TestFail tc o):xs) = do putStr ((show tc) ++ " failed\n")
                                       putStr (o ++ "\nvs\n" ++ (expected tc) ++ "\n--\n")
                                       printResults xs

-- | Perform a test and record its outcome.  There are six
-- possibilities: 1) positive test succeeds; 2) postive test
-- fail/non-parse (parse fails); 3) positive test error (unparse not
-- as expected); 4) negative test succeeds; 5) negative test
-- fail/parse (parse succeeds); 6) negative test error (error not as
-- expected).
performTest :: TestCase -> TestOutcome
performTest tc =
    case (sense tc, (parseTestCase tc)) of
      (Positive, Right o) -> if (trim o) == (trim (expected tc))
                             then TestPass tc -- case 1
                             else TestFail tc o -- case 3
      (Positive, Left err) -> TestFail tc (show err) -- case 2
      (Negative, Right o) -> TestFail tc o -- case 5
      (Negative, Left err) -> if (trim es) == (trim (expected tc))
                              then TestPass tc -- case 4
                              else TestFail tc es -- case 6
                                  where es = (show err)
        where trim = applyTwice (reverse . trim1)
              trim1 = dropWhile (`elem` delim) 
              delim = [' ', '\t', '\n', '\r']
              applyTwice f = f . f

-- | Run a test case.
parseTestCase :: TestCase -> Either ParseError String
parseTestCase t =
    case (parser t) of
      "CoreCspCASL" -> case (runParser basicCspCaslSpec es fn s) of
                         Left err -> Left err
                         Right x  -> Right (showDoc x "")
      "Process" -> case (runParser csp_casl_process es fn s) of
                     Left err -> Left err
                     Right x  -> Right (showDoc x "")
      _ -> error "Parser name"
    where es = emptyAnnos ()
          fn = src_file t
          s = src t
-- The above implemenation is horrible.  There must be a nice way to
-- abstract the parser out from the code to run it and collect/unparse
-- the result.  Alas, I don't know it, or don't know that I know it.

-- It's all I/O from here down.

-- | Given a path to a directory containing test cases, return a list
-- of test case values.
readAllTests :: FilePath -> IO [TestCase]
readAllTests path = do tests <- listTestCases path
                       mapM (readOneTestCase path) tests

-- | List every file in the test directory ending with '.testcase'
listTestCases :: FilePath -> IO [FilePath]
listTestCases path =
    do files <- getDirectoryContents path
       let cases = (map (\x -> path ++ "/" ++ x) (filter isTestCase files))
       return cases
    where
      endswith sub tgt = drop (length sub - length tgt) sub == tgt
      isTestCase f = endswith f ".testcase"


-- | Given the path to a .testcase file, return TestCase value
-- described therein.
readOneTestCase :: FilePath -> FilePath -> IO TestCase
readOneTestCase dir tc =
    do hdl <- openFile tc ReadMode
       contents <- hGetContents hdl
       let (a, b, c, d) = (interpret contents)
       hdl_s <- openFile (dir ++ "/" ++ a) ReadMode
       e <- hGetContents hdl_s
       return TestCase { src_file=a, parser=b, sense=c, expected=d,
                         src=e
                       }

-- | Given the textual content of a .testcase file, split it into
-- strings representing the various parts of the test case.
interpret :: String -> (String, String, TestSense, String)
interpret s = (head ls,
               head (tail ls),
               interpretSense (head (tail (tail ls))),
               unlines (tail (tail (tail ls))))
    where ls = lines s

-- | Interpret a test case sense (++ or --, positive or negative)
interpretSense :: String -> TestSense
interpretSense s = case s of
                     "++" ->  Positive
                     "--" -> Negative
                     _ -> error "Test sense"

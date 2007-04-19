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

Usage:

  testwrap targets

  where each target can be:

    - a .cspcasl file; parse the file as a Core-CspCASL specification,
      unparse the parse tree, and print out the result of the unparse.
      In case of parse error, report the error.

    - a .testcase file; execute the test and report the outcome.  A
      testcase file specifies one test case, whose source is contained
      in another file, and whose output we will check against expected
      contents.  See below for the file format.

    - a .testcases file; execute the tests and report their outcomes.
      A testcases file specifies multiple test cases, with source
      integrated with each test case, and outputs we will check
      against expected contents.  See below for the file format.

    - a directory; find all .cspcasl, .testcase and .testcases files
      in the directory (recursively) and operate on them as described
      above.

Postive & negative tests:

  A positive test is one where we expect the parse to succeed; here
  the expected output is the result of unparsing the resultant parse
  tree.  The test can fail with a parse error, or with unexpected
  output.

  A negative test is one where we expect the parse to fail; here the
  expected output is the error message produced.  The test can fail
  with a successful parse, or with unexpected output.

Format of .testcase files:

  A .testcase file contains a single test case.  The first line is the
  name of the file containing the source to be parsed/tested (it also
  acts as the name of the test case).  The second line identifies the
  test sense ("++" is positive, "--" is negative). The third line is
  the name of the parser to be used.  The remaining lines contain the
  expected output of the test.

Format of .testcases files:

  A .testcases file contains multiple test cases including their
  source.  Individual test cases are separated by lines containing
  twenty '-' characters and nothing else.  The format of an individual
  test case is similar but not identical to the format of a standalone
  test case (above).  The first line is the name of the test (used for
  reporting).  The second line identifies the test sense ("++" is
  positive, "--" is negative). The third line is the name of the
  parser to be used.  This is followed by the source of the test and
  the expected outcome of the test, both of which may span multiple
  lines; they are separated by a line containing ten '-' characters
  and nothing else.

-}

module Main where

import List
import Monad
import System.Directory
import System.Environment (getArgs)
import System.IO
import Text.ParserCombinators.Parsec

import Common.AnnoState (emptyAnnos)
import Common.DocUtils

import CspCASL.Parse_CspCASL(basicCspCaslSpec)
import CspCASL.Parse_CspCASL_Process(csp_casl_process)
import CspCASL.Print_CspCASL()

main :: IO ()
main = do args <- getArgs
          dirs <- filterM doesDirectoryExist args
          dir_contents <- (liftM concat) (mapM listFilesR dirs)
          candidates <- filterM doesFileExist (nub (args ++ dir_contents))
          parseCspCASLs (filter (".cspcasl" `isSuffixOf`) candidates)
          performTests (filter isTestCase candidates)
    where isTestCase f = (".testcase" `isSuffixOf` f) ||
                         (".testcases" `isSuffixOf` f)

-- | Given a list of paths to .cspcasl files, parse each in turn,
-- printing results as you go.
parseCspCASLs :: [FilePath] -> IO ()
parseCspCASLs [] = do putStr ""
parseCspCASLs (f:fs) = do putStrLn "--------------------"
                          prettyCspCASLFromFile f
                          parseCspCASLs fs

-- | Parse one .cspcasl file; print error or pretty print parse tree.
prettyCspCASLFromFile :: FilePath -> IO ()
prettyCspCASLFromFile fname
  = do putStrLn ("Parsing " ++ fname)
       input <- readFile fname
       case (runParser basicCspCaslSpec (emptyAnnos ()) fname input) of
           Left err -> do putStr "parse error at "
                          print err
           Right x  -> do putStrLn $ showDoc x ""

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

performTests :: [FilePath] -> IO ()
performTests tcs = do putStrLn "Performing tests"
                      print tcs


tcMain :: IO ()
tcMain = do contents <- readAllTests "test"
            printResults (map performTest (sort contents))

printResults :: [TestOutcome] -> IO ()
printResults [] = do putStr ""
printResults ((TestPass tc):xs) = do putStrLn ((show tc) ++ " passed")
                                     printResults xs
printResults ((TestFail tc o):xs) = do putStrLn ((show tc) ++ " failed")
                                       putStrLn (o ++ "\nvs\n" ++ (expected tc))
                                       putStrLn "--"
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

-- It's all file I/O from here down.

-- | Recursive file lister adapted from
-- http://therning.org/magnus/archives/228
listFilesR :: FilePath -> IO [FilePath]
listFilesR path =
    do allfiles <- getDirectoryContents path
       no_dots <- filterM (return . isDODD) (map (joinFN path) allfiles)
       dirs <- filterM doesDirectoryExist no_dots
       subdirfiles <- (mapM listFilesR dirs >>= return . concat)
       files <- filterM doesFileExist no_dots
       return $ files ++ subdirfiles
    where
      isDODD f = not $ ("/." `isSuffixOf` f) || ("/.." `isSuffixOf` f)
      joinFN p1 p2 = p1 ++ "/" ++ p2

-- | Given a path to a directory containing test cases, return a list
-- of test case values.
readAllTests :: FilePath -> IO [TestCase]
readAllTests path = do tests <- listTestCases path
                       mapM (readOneTestCase path) tests

-- | List every file in the test directory ending with '.testcase'
listTestCases :: FilePath -> IO [FilePath]
listTestCases path =
    do files <- getDirectoryContents path
       let cases = (map (\x -> path ++ "/" ++ x)
                            (filter (".testcase" `isSuffixOf`) files))
       return cases

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

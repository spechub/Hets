{- |
Module      :  $Id$
Copyright   :  (c) Andy Gimblett and Markus Roggenbach and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Test case wrapper for CspCASL specs and fragments.

This is a standalone `main' wrapper for CspCASL-related tests
performed locally to the CspCASL codebase.  It's probably only of
interest to the CspCASL maintainers.

Usage:

  testwrap [options] targets

Options:

  -t    Don't parse any .cspcasl files; useful for just running tests.

  -c    Don't run any tests; useful for just parsing .cspcasl files.

  Obviously, specifying both of these options stops this program from
  doing anything useful.

Parameters:

  targets - a list of targets, where each target can be:

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

Postive and negative tests:

  A positive test is one where we expect the parse to succeed; here
  the expected output is the result of unparsing the resultant parse
  tree.  The test can fail with a parse error, or with unexpected
  output.

  A negative test is one where we expect the parse to fail; here the
  expected output is the error message produced.  The test can fail
  with a successful parse, or with unexpected output.

Format of .testcase files:

  A .testcase file contains a single test case.  The first line is the
  path to the file containing the source to be parsed/tested, relative
  to the .testcase file; it also acts as the name of the test case.
  The second line identifies the test sense ("++" is positive, "--" is
  negative). The third line is the name of the parser to be used.  The
  remaining lines contain the expected output of the test.

Format of .testcases files:

  A .testcases file contains multiple test cases including their
  source.  Individual test cases are separated by lines containing
  twenty '-' characters and nothing else.  The format of an individual
  test case is similar but not identical to the format of a standalone
  test case (above).  The first line is the name of the test (used for
  reporting).  The second line identifies the test sense ("++" is
  positive, "--" is negative). The third line is the name of the
  parser to be used.  This is followed by the expected outcome of the
  test and the source (input) of the test, in that order, both of
  which may span multiple lines; they are separated by a line
  containing ten '-' characters and nothing else.

-}

module Main where

import Data.List
import Control.Monad
import System.Directory
import System.Environment (getArgs)
import System.FilePath (combine, dropFileName)
import System.IO
import Text.ParserCombinators.Parsec

import Common.AnnoState (emptyAnnos)
import Common.DocUtils

import CspCASL.Parse_CspCASL(cspBasicSpec)
import CspCASL.Parse_CspCASL_Process(csp_casl_process)
import CspCASL.Print_CspCASL()

main :: IO ()
main = do args <- getArgs
          dirs <- filterM doesDirectoryExist args
          dir_contents <- (liftM concat) (mapM listFilesR dirs)
          files <- filterM doesFileExist (sort $ nub (args ++ dir_contents))
          doIf ("-t" `notElem` args) (parseCspCASLs (filter isCspCASL files))
          doIf ("-c" `notElem` args) (performTests (filter isTest files))
    where isCspCASL = (".cspcasl" `isSuffixOf`)
          isTest f = (isSuffixOf ".testcase" f) || (isSuffixOf ".testcases" f)
          doIf c f = if c then f else putStr ""

-- | Given a list of paths to .cspcasl files, parse each in turn,
-- printing results as you go.
parseCspCASLs :: [FilePath] -> IO ()
parseCspCASLs [] = do putStr ""
parseCspCASLs (f:fs) = do putStrLn dash20
                          prettyCspCASLFromFile f
                          parseCspCASLs fs

-- | Parse one .cspcasl file; print error or pretty print parse tree.
prettyCspCASLFromFile :: FilePath -> IO ()
prettyCspCASLFromFile fname
  = do putStrLn ("Parsing " ++ fname)
       input <- readFile fname
       case (runParser cspBasicSpec (emptyAnnos ()) fname input) of
           Left err -> do putStr "parse error at "
                          print err
           Right x  -> do putStrLn $ showDoc x ""
                          putStrLn $ (show x)

-- | Test sense: do we expect parse success or failure?  What is the
-- nature of the expected output?
data TestSense = Positive | Negative
                 deriving (Eq, Ord)
instance Show TestSense where
  show Positive = "++"
  show Negative = "--"

-- | Test case details: where is source, what is it, which parser, etc.
data TestCase = TestCase {
      -- | @name@ - test name
      name :: String,
      -- | @parser@ - name of parser to apply
      parser :: String,
      -- | @sense@ - sense of test (positive or negative)
      sense :: TestSense,
      -- | @src@ - source to be parsed
      src :: String,
      -- | @expected@ - expected output of test
      expected :: String
} deriving (Eq, Ord)
instance Show TestCase where
  show a = (name a) ++ " (" ++ (show (sense a)) ++ (parser a) ++ ")"

-- | Given a list of paths of test case files, read & perform them.
performTests :: [FilePath] -> IO ()
performTests tcs = do putStrLn "Performing tests"
                      tests <- (liftM concat) (mapM readTestFile tcs)
                      doTests tests

-- | Turn a .testcase or .testcases file into list of test cases therein.
readTestFile :: FilePath -> IO [TestCase]
readTestFile f
    | ".testcase"  `isSuffixOf` f = readTestCaseFile f
    | ".testcases" `isSuffixOf` f = readTestCasesFile f
    | otherwise                   = do return []

-- | Turn a .testcase file into the test case therein.
readTestCaseFile :: FilePath -> IO [TestCase]
readTestCaseFile f =
    do hdl <- openFile f ReadMode
       contents <- hGetContents hdl
       let (a, b, c, d) = (testCaseParts contents)
       hdl_s <- openFile (combine (dropFileName f) a) ReadMode
       e <- hGetContents hdl_s
       return [TestCase { name=a, parser=b, sense=c, expected=d, src=e }]

-- | Turn a .testcases file into the test cases therein.
readTestCasesFile :: FilePath -> IO [TestCase]
readTestCasesFile f =
    do hdl <- openFile f ReadMode
       s <- hGetContents hdl
       let tests = map interpretTestCasesOne (map strip (split dash20 s))
       return tests

-- | Turn test case string from a .testcases file into its test case.
interpretTestCasesOne :: String -> TestCase
interpretTestCasesOne s
    | (length parts) == 2 = TestCase { name=a, parser=b, sense=c,
                                       expected=d, src=e }
    | otherwise = error s
    where parts = map strip (split dash10 s)
          (a, b, c, d) = testCaseParts (parts !! 0)
          e = parts !! 1

-- | Turn test case string into its constituent parts (except source).
testCaseParts :: String -> (String, String, TestSense, String)
testCaseParts s = (head ls,
                   head (tail ls),
                   interpretSense (head (tail (tail ls))),
                   unlines (tail (tail (tail ls))))
    where ls = lines s

-- | Interpret a test case sense (++ or --, positive or negative)
interpretSense :: String -> TestSense
interpretSense s = case s of
                     "++" ->  Positive
                     "--" -> Negative
                     _ -> error ("Bad test sense " ++ s)

-- | Given a list of test cases, perform the tests in turn, printing
-- results as you go.
doTests :: [TestCase] -> IO ()
doTests [] = do putStr ""
doTests (tc:ts) = do --putStrLn dash20
                     let output = parseTestCase tc
                     putStr ((show tc) ++ " ")
                     printOutcome tc output
                     doTests ts

-- | Perform a test and report its outcome.  There are six
-- possibilities: 1) positive test succeeds; 2) postive test
-- fail/non-parse (parse fails); 3) positive test error (unparse not
-- as expected); 4) negative test succeeds; 5) negative test
-- fail/parse (parse succeeds); 6) negative test error (error not as
-- expected).
printOutcome :: TestCase -> Either ParseError (String, String) -> IO ()
printOutcome tc out =
    case (sense tc, out) of
      (Positive, Right (o, tree)) ->
          if (strip o) == (strip $ expected tc)
          then testPass                                    -- case 1
          else do testFail "unparse" (expected tc) o       -- case 3
                  putStrLn ("-> tree:\n" ++ tree)
      (Positive, Left err) ->
          testFail "parse failure" "" (show err)        -- case 2
      (Negative, Right (o, _)) ->
          testFail "parse success" (expected tc) o         -- case 5
      (Negative, Left err) ->
          if (strip $ show $ err) == (strip $ expected tc)
          then testPass                                    -- case 4
          else testFail "error" (expected tc) (show err)   -- case 6

-- Report on a test pass
testPass :: IO ()
testPass = do putStrLn "passed"

-- Report on a test failure
testFail :: String -> String -> String -> IO()
testFail nature expect got =
    do putStrLn ("failed - unexpected " ++ nature)
       if expect /= ""
          then putStrLn ("-> expected:\n" ++ (strip expect))
          else putStr ""
       putStrLn "-> got:"
       putStrLn $ strip got


-- | Run a test case through its parser.
parseTestCase :: TestCase -> Either ParseError (String, String)
parseTestCase t =
    case (parser t) of
      "CoreCspCASL" -> case (runWithEof cspBasicSpec) of
                         Left err -> Left err
                         Right x  -> Right ((showDoc x ""), (show x))
      "Process" -> case (runWithEof csp_casl_process) of
                     Left err -> Left err
                     Right x  -> Right ((showDoc x ""), (show x))
      _ -> error "Parser name"
    where runWithEof p = runParser p' (emptyAnnos ()) (name t) (src t)
              where p' = do n <- p
                            eof
                            return n

-- The above implemenation is horrible.  There must be a nice way to
-- abstract the parser out from the code to run it and collect/unparse
-- the result.  Alas, I don't know it, or don't know that I know it.

dash20, dash10 :: String
dash10 = "----------"
dash20 = dash10 ++ dash10

-- Utility functions which really should be in the standard library!

-- | Recursive file lister adapted from
-- http://therning.org/magnus/archives/228
listFilesR :: FilePath -> IO [FilePath]
listFilesR path =
    do allfiles <- getDirectoryContents path
       nodots <- filterM (return . isDODD) (map (combine path) allfiles)
       dirs <- filterM doesDirectoryExist nodots
       subdirfiles <- (mapM listFilesR dirs >>= return . concat)
       files <- filterM doesFileExist nodots
       return $ files ++ subdirfiles
    where
      isDODD f = not $ ("/." `isSuffixOf` f) || ("/.." `isSuffixOf` f)

-- | A function inspired by python's string.split().  A list is split
-- on a separator which is itself a list (not a single element).
split :: Eq a => [a] -> [a] -> [[a]]
split tok splitme = unfoldr (sp1 tok) splitme
    where sp1 _ [] = Nothing
          sp1 t s = case find (t `isSuffixOf`) $ (inits s) of
                      Nothing -> Just (s, [])
                      Just p -> Just (take (length p - length t) p,
                                      drop (length p) s)

-- | String strip in style of python string.strip()
strip :: String -> String
strip s = dropWhile ws $ reverse $ dropWhile ws $ reverse s
    where ws = (`elem` [' ', '\n', '\t', '\r'])

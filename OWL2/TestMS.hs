
module OWL2.TestMS where

import System.Process
import System.Environment
import System.IO
import System.Directory
import Data.List as L (sort,isSuffixOf, isPrefixOf, (\\), sortOn)
import qualified Data.Set as S (fromList, difference, null, size)
import Data.Map(empty, unions)
import Control.Monad

import Common.Parsec
import Text.ParserCombinators.Parsec

import Text.Read(readMaybe)


import Common.DocUtils (pretty)
import OWL2.AS
-- import OWL2.PrintMS
import OWL2.ParseMS

data Option = SkipSuccessful | OnlyParse | MaxSize Int | Exclude FilePath deriving Eq

instance Show Option where
    show SkipSuccessful = "--skipSuccessful"
    show OnlyParse = "--onlyParse"
    show (MaxSize i) = "--maxSize=" ++ show i
    show (Exclude s) = "--exclude=" ++ s

skipSuccessful :: [Option] -> Bool
skipSuccessful = elem SkipSuccessful

onlyParse :: [Option] -> Bool
onlyParse = elem OnlyParse

maxSize :: [Option] -> Maybe Integer
maxSize = foldr (\x _ -> case x of
    MaxSize i -> Just (fromIntegral i)
    _ -> Nothing
  ) Nothing

excluded :: [Option] -> [FilePath]
excluded = foldr (\o a -> case o of
    Exclude s -> s : a
    _ -> a
  ) []



data TestResult = Success | ParsingSourceFailed | ParsingPrintedFailed | DifferentAxioms | Skipped

stat_successful :: [TestResult] -> Int
stat_successful = sum . fmap (\t -> case t of {Success -> 1; _ -> 0})
stat_sourceFailed :: [TestResult] -> Int
stat_sourceFailed = sum . fmap (\t -> case t of {ParsingSourceFailed -> 1; _ -> 0})
stat_printedFailed :: [TestResult] -> Int
stat_printedFailed = sum . fmap (\t -> case t of {ParsingPrintedFailed -> 1; _ -> 0})
stat_differentAxioms :: [TestResult] -> Int
stat_differentAxioms = sum . fmap (\t -> case t of {DifferentAxioms -> 1; _ -> 0})
stat_skipped :: [TestResult] -> Int
stat_skipped = sum . fmap (\t -> case t of {Skipped -> 1; _ -> 0})

runTest :: [Option] -> FilePath -> FilePath -> IO TestResult
runTest opts d f = do
    let path = d ++ "/" ++ f ++ ".success"
    e <- doesFileExist path
    if skipSuccessful opts && e then return Skipped else runTest' opts d f

runTest' :: [Option] -> FilePath -> FilePath -> IO TestResult
runTest' opts d f
  | f `elem` excluded opts = return Skipped
  | otherwise = do
    let path = d ++ "/" ++ f
    content <- readFile path
    putStrLn $ "\x1b[38;2;40;177;249mTesting '" ++ path ++ "'" ++ "\x1b[0m"
    if onlyParse opts then return () else putStrLn "  Parsing Source File"
    let res = parse (parseOntologyDocument mempty) f content

    if onlyParse opts then (either (\e -> putStrLn ("  ❌ Parsing Source Failed: " ++ show e) >> return ParsingSourceFailed) (const (putStrLn "  ✅ Parsing Source Succeeded"  >> return Success)) res) else putStrLn "  ❌ Printing not implemented"  >> return ParsingPrintedFailed
        -- case res of
        --         Left e -> putStrLn ("    ⚡ Parsing Source Failed: " ++ show e) >> return ParsingSourceFailed
        --         Right o@(OntologyDocument _ (Ontology _ _ _ _ ax)) -> do
        --             callCommand $ "touch " ++ path ++ ".parsed1"
        --             writeFile (path ++ ".parsed1") (show o)
        --             putStrLn "  Parsing Printed Document"
        --             let content2 = show $ pretty o
        --             let res2 = parse (parseOntologyDocument mempty) f content2
        --             case res2 of
        --                     Left e -> do
        --                         putStrLn ("    ❌ Parsing Printed Failed: \x1b[38;2;255;56;43m" ++ show e ++ "\x1b[0m")
        --                         callCommand $ "touch " ++ path ++ ".printed"
        --                         writeFile (path ++ ".printed") content2
        --                         return ParsingPrintedFailed
        --                     Right o2@(OntologyDocument _ (Ontology _ _ _ _ ax2)) ->
        --                         let diff = S.difference (S.fromList ax) (S.fromList ax2) in
        --                         if S.null diff
        --                             then do
        --                                 callCommand $ "touch " ++ path ++ ".success"
        --                                 putStrLn "  ✅ Success" 
        --                                 return Success
        --                             else do 
        --                                 callCommand $ "touch " ++ path ++ ".parsed2"
        --                                 writeFile (path ++ ".parsed2") (show o2)
        --                                 callCommand $ "touch " ++ path ++ ".printed"
        --                                 writeFile (path ++ ".printed") content2
        --                                 callCommand $ "touch " ++ path ++ ".differentaxioms"
        --                                 writeFile (f ++ ".differentaxioms") (show $ diff)
        --                                 putStrLn ("    ❌ Axioms are not identical: \x1b[38;2;255;56;43m" ++ show (S.size diff) ++ " different axioms of " ++ show (length ax) ++ "/" ++ show (length ax2) ++ "\x1b[0m")
        --                                 return $ DifferentAxioms

-- parses all file in given directories and displays whether parsing was successful
runAllTestsInDir :: [Option] -> FilePath -> IO [TestResult]
runAllTestsInDir opts d = do
    contents <- filter (isSuffixOf ".omn") <$> getDirectoryContents d
    sizes <- mapM (\f -> getFileSize (d ++ "/" ++ f)) contents
    let fs = zip contents sizes
    let files = (fst <$> sortOn snd fs)
    -- excluded <- filterM (\f -> getFileSize (d ++ "/" ++ f) >>= return . (>= 10000*1024*1024)) files
    excluded <- maybe (return []) (\s -> filterM (\f -> getFileSize (d ++ "/" ++ f) >>= return . (>= s)) files) (maxSize opts)
    r <- sequence (runTest opts d <$> (files \\ excluded))
    return $ r ++ (map (const Skipped) excluded)

-- tests parsing on all OWL2/tests/**/*.ofn files
pta :: [Option] -> IO ()
pta opts = do 
  stats <- sequence (runAllTestsInDir opts <$> dirs) >>= return . concat
  let successful = stat_successful stats
  let skipped = stat_skipped stats
  let failedSourceParsing = stat_sourceFailed stats
  let failedPrintedParsing = stat_printedFailed stats
  let differentAxioms = stat_differentAxioms stats
  let total = length stats
  let ratio =  successful * 100 `div` total * 100 `div` 100
  putStrLn $ show successful ++ "/" ++ show total ++ " (" ++ show ratio ++"%) tests passed.\n  Skipped: " ++ show skipped ++ "\n  Parsing Source Failed: " ++ show failedSourceParsing ++ "\n  \x1b[38;2;255;56;43mParsing Printed failed: " ++ show failedPrintedParsing ++ "\n  Different Axioms: " ++ show differentAxioms ++ "\x1b[0m\n"
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
            "./_bioportal"]

-- parses the test.ofn file in the current directory and prints the result
pt :: IO ()
pt = do
    runTest [] "." "test.omn"
    return ()
    
-- parses the test.ofn file in the current directory and prints the result
ps :: IO ()
ps = do
    content <- readFile "./test.omn"
    let res = parse (parseOntologyDocument mempty) "" content
    putStrLn $ either (\e -> "❌ Failed:\n" ++ show e) (const "✅ Success") res

    return ()

-- getFileSize :: FilePath -> IO (Integer)
-- getFileSize path = handle (return 0) $ bracket (openFile path ReadMode) (hClose) hFileSize

toOpt :: String -> Maybe Option
toOpt s
    | s == show SkipSuccessful = Just SkipSuccessful
    | s == show OnlyParse = Just OnlyParse
    | "--maxSize=" `isPrefixOf` s = Just $ MaxSize $ read $ s \\ "--maxSize="
    | otherwise = Nothing

extractOpts :: [String] -> [Option]
extractOpts = foldr (\s a -> maybe a (:a) (toOpt s) ) []

main :: IO ()
main = do
    args <- getArgs
    let opts = extractOpts args
    let files = filter (not . isPrefixOf "--") args
    if null files then pta opts else (sequence $ runTest opts "." <$> files) >> return ()


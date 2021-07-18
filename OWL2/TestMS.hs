
import System.Process
import System.IO
import System.Directory
import Data.List as L (sort,isSuffixOf, (\\))
import Data.Set as S (fromList, difference, null, size)
import Data.Map(empty)
import Control.Monad

import Common.Parsec
import Text.ParserCombinators.Parsec


import Common.DocUtils (pretty)
import OWL2.AS
import OWL2.PrintMS
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
        runTest :: FilePath -> IO Int
        runTest f = do
            let path = d ++ "/" ++ f            
            content <- readFile path
            putStrLn $ "\x1b[38;2;40;177;249mTesting '" ++ path ++ "'" ++ "\x1b[0m"
            putStrLn "  Parsing Source File"
            let res = parse (parseOntologyDocument mempty) f content
            case res of
                    Left e -> putStrLn ("    ⚡ Parsing Source Failed: " ++ show e) >> return 0
                    Right o@(OntologyDocument _ (Ontology _ _ _ _ ax)) -> do
                        putStrLn "  Parsing Printed Document"
                        let content2 = show $ pretty o
                        let res2 = parse (parseOntologyDocument mempty) f content2
                        case res2 of
                                Left e -> do
                                    putStrLn ("    ❌ Parsing Printed Failed: \x1b[38;2;255;56;43m" ++ show e ++ "\x1b[0m")
                                    callCommand $ "touch " ++ f ++ ".printed"
                                    writeFile (f ++ ".printed") content2
                                    return 0
                                Right (OntologyDocument _ (Ontology _ _ _ _ ax2)) ->
                                    let diff = difference (S.fromList ax) (S.fromList ax2) in
                                    if S.null diff
                                        then putStrLn "  ✅ Success" >> return 1
                                        else do 
                                            callCommand $ "touch " ++ f ++ ".differentaxioms"
                                            writeFile (f ++ ".differentaxioms") (show $ diff)
                                            putStrLn ("    ❌ Axioms are not identical: \x1b[38;2;255;56;43m" ++ show (size diff) ++ " different axioms of " ++ show (length ax) ++ "/" ++ show (length ax2) ++ "\x1b[0m") >> return 0

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
            "../HetsOwlTest/tmp"]

-- parses the test.ofn file in the current directory and prints the result
pt :: IO ()
pt = do
    content <- readFile "./test.omn"
    putStrLn "Parsing Source File"
    let res = parse (parseOntologyDocument mempty) "" content
    case res of
            Left e -> putStrLn ("  ⚡ Parsing Source Failed: " ++ show e) >> return 0
            Right o@(OntologyDocument _ (Ontology _ _ _ _ ax)) -> do
                putStrLn "Parsing Printed Document"
                let content2 = show $ pretty o
                let res2 = parse (parseOntologyDocument mempty) "" content2
                case res2 of
                        Left e -> putStrLn ("  ❌ Parsing Printed Failed: " ++ show e) >> return 0
                        Right (OntologyDocument _ (Ontology _ _ _ _ ax2)) ->
                            let diff = difference (S.fromList ax) (S.fromList ax2) in
                            if S.null diff
                                then putStrLn "  ✅ Success" >> return 1
                                else putStrLn ("  ❌ Axioms are not identical: " ++ (show diff)) >> return 0
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

main :: IO ()
main = pta


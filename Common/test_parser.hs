module Main where

import System.Environment
import Data.List

import Text.ParserCombinators.Parsec
import qualified Common.CaslLanguage as L(casl_id, semi, whiteSpace)
import Common.AnnoParser
import Common.DocUtils
import Common.Id
import Common.Token(parseId)

testP :: Show a => (b -> a) -> CharParser () b -> SourceName -> String -> IO ()
testP f p n s = case parse p n s of
             Left err -> putStr "parse error at " >> print err
             Right x  -> print $ f x

cleanP :: CharParser () a -> CharParser () a
cleanP p = do {L.whiteSpace ; res <- p; eof ; return res}

testPL :: Show a => CharParser () a -> String -> IO ()
testPL par inp = testP id (cleanP par) "" inp

parseFile :: Pretty a => CharParser () a -> FilePath -> IO ()
parseFile par name = do
    inp <- readFile name
    testP pretty (cleanP par) name inp

testFile :: Pretty a => CharParser () a -> FilePath -> IO ()
testFile par name = do
    inp <- readFile name
    mapM_ (testLine par) $ lines inp
    where testLine p line = do
            putStr "** Input was: "
            print line
            putStr "** Result is: "
            testPL p line

testFileC :: FilePath -> IO ()
testFileC name = do
    inp <- readFile name
    mapM_ testLine $ lines inp
    where testLine line = showDiff line (test_id L.casl_id line)
                          $ test_id (parseId []) line

testData :: CharParser () a -> String -> Either ParseError a
testData p s = parse (do {L.whiteSpace ; res <- p; eof ; return res}) "" s

test_id :: CharParser () Id -> String -> IO ()
test_id p inp = case testData p inp of
  Left err -> print err
  Right ide -> printId ide


-- Comparing Id-Parser and presenting results
testFileCS :: FilePath -> IO ()
testFileCS name = do
  inp <- readFile name
  ((ma,dif),rl) <- return $ mapAccumL testLine (0, 0) (lines inp)
  sequence rl
  putStrLn $ "------\nMatched: " ++ show ma ++
               "\nDiffs: " ++ show dif
  where testLine (ma,dif) line =
              let res1 = testData L.casl_id line
                  res2 = testData (parseId []) line
                  (ma1,dif1,out) = comp res1 res2 line
              in ((ma + ma1 :: Int, dif + dif1 :: Int), out)

comp :: Either ParseError Id -> Either ParseError Id -> String
     -> (Int, Int, IO ())
comp (Left err1) (Left err2) line =
    (0,0,showDiff line (print err1) (print err2))
comp (Left err1) (Right id2) line =
    (0,1,showDiff line (print err1) (printId id2))
comp (Right id1) (Left err2) line =
    (0,1,showDiff line (printId id1) (print err2))
comp (Right id1) (Right id2) line =
              if id1 == id2 then (1 :: Int, 0 :: Int, putStr "")
              else if showId id1 "" == showId id2 "" then diff_rep
                   else diff_parse where
          diff_parse = (0,1,putStrLn "Different Parses!" >> diff)
          diff_rep = (1,0, putStrLn "Diferent Representations!" >> diff)
          diff = showDiff line (printId id1) (printId id2)

showDiff :: String -> IO () -> IO () -> IO ()
showDiff line out1 out2 =
    do putStr "** Input was: "
       putStrLn line
       putStr "** Result(KL) is: "
       out1
       putStr "** Result(CM) is: "
       out2

printId :: Id -> IO ()
printId ide@(Id _ comps _) = do
    if null comps then putChar 'M' else putChar 'C'
    putStr ": "
    putStrLn (showId ide "")

-- call it with "-p {casl_id, casl_id2} <files>"
main :: IO ()
main = do
    as <- getArgs
    (p,files) <- return (extract_par as)
    mapM_ (parseFile' p) files
    where extract_par = extract_par' "annotations" []
          extract_par' p ac args = case args of
             [] -> error
                   "usage: <prog> -p (annotation|casl_id|casl_id2) <files>"
             [_] -> (p,ac ++ args)
             x:ltl@(y:tl) -> if x == "-p"
                             then extract_par' y ac tl
                             else extract_par' p (ac++x:[]) (ltl)
          parseFile' s = case s of
                         "annotations" -> parseFile annotations
                         "casl_id"     -> testFileC
                         "casl_id2"    -> testFileCS
                         _             -> error ("*** unknown parser " ++ s)

testId :: IO ()
testId = testPL (sepBy L.casl_id L.semi)
         "__++__ ; __+*[y__,a_l'__,4]__ ; {__}[__] ; __a__b[__z]"

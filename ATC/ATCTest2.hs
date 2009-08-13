module Main where

import System.Environment
import System.Random
import ATerm.SimpPretty
import ATerm.Lib
import ATerm.ReadWrite
import ATerm.Unshared
import Common.Utils (readMaybe)
import qualified Data.Map as Map
import Data.List (isPrefixOf)

main :: IO ()
main = do args <- getArgs
          setStdGen (mkStdGen 50) -- setting an initial RandomGenerator
                                  -- is like setting the seed in C
          let (cmd,files) = (head args,tail args)
          let cmdFun = case cmd of
                       "ReadWrite" -> testATC
                       cmds
                           | isPrefixOf "BigMap" cmds  ->
                               testDDataMap (drop 6 cmds)
                           | isPrefixOf "BigList" cmds  ->
                               testListConv (drop 7 cmds)
                           | isPrefixOf "CheckBigMap" cmds ->
                               checkDDataMap (drop 11 cmds)
                           | isPrefixOf "CheckBigList" cmds ->
                               checkListConv (drop 12 cmds)
                           | otherwise           -> usage cmd
          mapM_ cmdFun files

usage :: String -> FilePath -> IO ()
usage cmd _ = do
  putStrLn ("unknown command: "++cmd)
  putStrLn ("Known commands are: ReadWrite, [Check]Big{Map,List}<n>")
  fail "no known command given"

generateRandomLists :: String -> IO [(Int,Int)]
generateRandomLists upstr  = do
    up <- case readMaybe upstr of
      Just u -> do
        putStrLn $ "generating list with "++ show u ++ " items"
        return u
      Nothing -> do
        putStrLn "no upper_number read"
        putStrLn "generating list with 2000 items"
        return 2000
    genIList up

genIList :: Int -> IO [(Int,Int)]
genIList cnt
    | cnt <= 0  = return []
    | otherwise = do v <- getStdRandom (randomR (1,maxBound::Int))
                     l <- genIList (cnt-1)
                     return ((cnt,v):l)

testDDataMap :: String ->  FilePath -> IO ()
testDDataMap upperstr fp = do
                  int_list <- generateRandomLists upperstr
                  let int_map = (Map.fromList int_list)
                  att0 <- newATermTable
                  (int_att,selectedATermIndex) <- toShATerm' att0 int_map
                  putStrLn $ show (getTopIndex int_att,selectedATermIndex)
                  writeFileSDoc fp $
                       writeSharedATermSDoc int_att
                  putStrLn "File written\nstart reading"
                  str <- readFile fp
                  let read_map :: Map.Map Int Int
                      read_map = fromShATerm (readATerm str)
                  putStrLn ("BigMap of Int -> Int is " ++
                            (if read_map == int_map
                             then "consistent."
                             else "inconsistent!!"))

checkDDataMap :: String ->  FilePath -> IO ()
checkDDataMap upperstr fp = do
                  int_list <- generateRandomLists upperstr
                  let int_map = (Map.fromList int_list)
                  str <- readFile fp
                  let read_map = fromShATerm (readATerm str)
                  putStrLn ("BigMap of Int -> Int is " ++
                            (if read_map == int_map
                             then "consistent."
                             else "inconsistent!!"))

testListConv :: String ->  FilePath -> IO ()
testListConv upperstr fp = do
                  int_list <- generateRandomLists upperstr
                  att0 <- newATermTable
                  (int_att,selectedATermIndex) <-
                          toShATerm' att0 $ reverse int_list
                  putStrLn $ show (getTopIndex int_att,selectedATermIndex)
                  writeFileSDoc fp $
                       writeSharedATermSDoc int_att
                  putStrLn "File written\nstart reading"
                  str <- readFile fp
                  let read_list :: [(Int,Int)]
                      read_list = fromShATerm (readATerm str)
                  putStrLn ("BigList of (Int,Int) is " ++
                            (if read_list == reverse int_list
                             then "consistent."
                             else "inconsistent!!"))

checkListConv :: String ->  FilePath -> IO ()
checkListConv upperstr fp = do
                  int_list <- generateRandomLists upperstr
                  str <- readFile fp
                  let read_list = fromShATerm (readATerm str)
                  putStrLn ("BigList of (Int,Int) is " ++
                            (if read_list == reverse int_list
                             then "consistent."
                             else "inconsistent!!"))


resultFP :: String -> String
resultFP fp = fp++".ttttt"


testATC :: FilePath -> IO ()
testATC fp = do str <- readFile fp
                let att = readATerm str
                putStrLn ("Reading File "++fp++" ...")
                let fp' = resultFP fp
                putStrLn ("Writing File "++fp'++" ...")
                writeFileSDoc fp' (writeSharedATermSDoc att)

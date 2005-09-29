module Main where

import System
import Data.List
import GHC.Read
import System.Random
-- import Options
-- import Common.Utils
import Common.SimpPretty
-- import Syntax.AS_Library
import Common.ATerm.Lib
import qualified Common.Lib.Map as Map
import Data.Array
import Data.FiniteMap
-- import WriteFn
-- import ReadFn

getTenRandoms :: IO [Int]
getTenRandoms = getRand 10
    where getRand x
              | x <= 0    = return []
              | otherwise = do y <- getStdRandom (randomR (1,6))
                               ys <- getRand (x-1)
                               return (y:ys)

main :: IO ()
main = do args <- getArgs
          setStdGen (mkStdGen 50) -- setting an initial RandomGenerator 
                                  -- is like setting the seed in C 
--        tens <- getTenRandoms
        --  putStrLn (show tens)
          --fail "stop"
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
usage cmd _ = do putStrLn ("unknown command: "++cmd)
                 putStrLn ("Known commands are: ReadWrite, BigMap, BigRel, BigSet")
                 fail "no known command given" 

generateRandomLists :: String -> IO ([(Int,Int)],[(Int,String)])
generateRandomLists upstr  = do
    up <- case readEither upstr of
          Right u -> do putStrLn ("generating list with "++show u
                                  ++" items")
                        return u
          Left  m -> do putStrLn ("no upper_number read\n"++
                                  m++"\ngenerating list with 2000 items")
                        return 2000
    str <- readFile "ATC/Haskell.header.hs"
    let strs = words str
        arrStr = listArray (0,length strs - 1) strs
    ilist <- genIList up
    strlist <- genSList arrStr up
    return (ilist,strlist)

genIList :: Int -> IO [(Int,Int)]
genIList cnt
    | cnt <= 0  = return []
    | otherwise = do v <- getStdRandom (randomR (1,maxBound::Int))
                     l <- genIList (cnt-1)
                     return ((cnt,v):l)

genSList :: Array Int String -> Int -> IO [(Int,String)]
genSList strs cnt = do
    ilist <- genIList cnt
    return (map trans ilist)
    where trans :: (Int,Int) -> (Int,String)
          trans (i,j) = (i,strs ! (j `mod` (snd (bounds strs) + 1)))

testDDataMap :: String ->  FilePath -> IO ()
testDDataMap upperstr fp = do
                  (int_list,str_list) <- generateRandomLists upperstr
                  let int_map = (Map.fromList int_list)
                      (int_att,selectedATermIndex) =
                          (toShATerm emptyATermTable int_map)
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
                  (int_list,str_list) <- generateRandomLists upperstr
                  let int_map = (Map.fromList int_list)
                  str <- readFile fp
                  let read_map = fromShATerm (readATerm str)
                  putStrLn ("BigMap of Int -> Int is " ++
                            (if read_map == int_map
                             then "consistent."
                             else "inconsistent!!"))

testListConv :: String ->  FilePath -> IO ()
testListConv upperstr fp = do
                  (int_list,str_list) <- generateRandomLists upperstr
                  let (int_att,selectedATermIndex) =
                          (toShATerm emptyATermTable (reverse int_list))
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
                  (int_list,str_list) <- generateRandomLists upperstr
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

                


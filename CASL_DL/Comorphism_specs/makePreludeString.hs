module Main where

import System.Environment

main :: IO ()
main = do
    let preludeFileName = "tmp.casl"
    preludeString <- readFile preludeFileName
    putStrLn (show preludeString)

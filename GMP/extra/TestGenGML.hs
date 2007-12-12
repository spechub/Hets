module Main where

import GMP.GMPAS

main :: IO()
main = do
    let f = T::Formula GML
    putStrLn(show f)

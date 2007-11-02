module Main where

import GMP.InequalitySolver

printResult :: [Int] -> [Int] -> Int -> IO ()
printResult n p lim =
    let res = ineqSolver (Coeffs n p) lim
    in putStr ("Solutions: " ++ show res ++ "\n")

st :: ([Int], [Int], Int) -> [Int]
st = \(x,_,_)->x

nd :: ([Int], [Int], Int) -> [Int]
nd = \(_,x,_)->x

rd :: ([Int], [Int], Int) -> Int
rd = \(_,_,x)->x

main :: IO()
main = do
{-    
    let i = ([],[],0)
    putStr ("Coefficients: " ++ show (st i) ++ " " ++ show (nd i)++ "\n")
    printResult (st i) (nd i) (rd i)

    let i = ([-13],[1],256)
    putStr ("Coefficients: " ++ show (st i) ++ " " ++ show (nd i)++ "\n")
    printResult (st i) (nd i) (rd i)
-}
    
    let i = ([],[],0)
    putStr ("Coefficients: " ++ show (st i) ++ " " ++ show (nd i)++ "\n")
    printResult (st i) (nd i) (rd i)

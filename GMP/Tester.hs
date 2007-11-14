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
    let i1 = ([],[],0)
    putStr ("Coefficients: " ++ show (st i1) ++ " " ++ show (nd i1)++ "\n")
    printResult (st i1) (nd i1) (rd i1)
    line <- getLine
    let i2 = ([13],[1],20)
    putStr ("Coefficients: " ++ show (st i2) ++ " " ++ show (nd i2)++ "\n")
    printResult (st i2) (nd i2) (rd i2)
    line <- getLine
    let i3 = ([1],[1],4)
    putStr ("Coefficients: " ++ show (st i3) ++ " " ++ show (nd i3)++ "\n")
    printResult (st i3) (nd i3) (rd i3)
    line <- getLine
    let i4 = ([2,3],[1],10)
    putStr ("Coefficients: " ++ show (st i4) ++ " " ++ show (nd i4)++ "\n")
    printResult (st i4) (nd i4) (rd i4)

{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}

data Natx a = Zx | Sx a (Natx a)

fun1 :: Natx Int -> (Natx Int, Int)
fun1 x = case x of 
       Zx -> (Zx, 0) 
       Sx n k -> (Sx n (fst (fun1 k)), n * (fun2 k))

fun2 :: Natx Int -> Int 
fun2 x = case x of 
   Zx -> 0
   Sx n k -> (snd (fun1 k)) + n 


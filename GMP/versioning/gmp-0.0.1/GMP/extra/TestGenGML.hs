{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import GMP.GMPAS

rg1 :: Formula GML -> Formula GML -> Int -> (Formula GML, Formula GML)
rg1 a b n = (Mapp (Mop (GML (n+1)) Angle) a, 
             Mapp (Mop (GML n) Angle) b)

a1 :: Formula GML -> Formula GML -> Formula GML -> Int -> Int -> (Formula GML, Formula GML, Formula GML)
a1 c a b n1 n2 = (Mapp (Mop (GML (n1+n2)) Angle) c, 
                  Mapp (Mop (GML n1) Angle) a, 
                  Mapp (Mop (GML n2) Angle) b)

a2 :: Formula GML -> Formula GML -> Formula GML -> Formula GML -> Int -> Int -> (Formula GML, Formula GML, Formula GML)
a2 a b c d n1 n2 = (Junctor (Mapp (Mop (GML n1) Angle) a) And (Mapp (Mop (GML n2) Angle) b),
                    Mapp (Mop (GML (n1+n2+1)) Angle) c,
                    Mapp (Mop (GML 0) Angle) d)

rn :: Formula GML -> Formula GML
rn a = Neg (Mapp (Mop (GML 0) Angle) (Neg a))

wrap2 :: Formula GML -> Formula GML -> Formula GML
wrap2 a b = Junctor a If b

wrap3 :: Formula GML -> Formula GML -> Formula GML -> (Formula GML,Formula GML)
wrap3 a b c = (a, Junctor b Or c)

recurse na1 nrg1 = 
  let a2_res = a2 (Var 'a' Nothing) (Var 'b' Nothing) (Junctor (Var 'a' Nothing) Or (Var 'b' Nothing)) (Var 'a' Nothing) 1 2
      rec_a1 (x,y,z) n = 
        case n of
          0 -> wrap3 x y z
          _ -> rec_a1 (a1 x y z 3 4) (n-1)
      a1_res = rec_a1 a2_res na1
      rec_rg1 (x,y) n =
        case n of
          0 -> wrap2 x y
          _ -> rec_rg1 (rg1 x y 5) (n-1)
  in rec_rg1 a1_res nrg1
    
main :: IO()
main = do
    let f = Neg (recurse 2 3)
    putStrLn(show f)

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


funOne :: Eq a => [a] -> [a] -> Bool
myMap :: [a] -> (a -> b) -> [b]

funOne x y = if x == (head x):(tail y) then True else False

myMap x f = case x of 
  [] -> []
  a:as -> (f a): myMap as f  


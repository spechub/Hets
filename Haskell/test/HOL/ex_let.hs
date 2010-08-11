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

myEqual        :: Eq a => a -> a -> Bool
myEqual x y    =   if x == y then True else False

foon :: Bool -> Bool -> Bool -> Bool
foon a b c = let 
 testName1 = myEqual a b 
 testName2 = myEqual b c 
 in
 testName1 && testName2


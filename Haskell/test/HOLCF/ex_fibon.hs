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


fibon :: Int -> Int
fibon n = if n == 0 then 1 else if n == 1 then 1 else fibon (n - 1) + fibon (n - 2)



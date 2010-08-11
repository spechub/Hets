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
import Common.XUpdate
import Control.Monad.Error

main :: IO ()
main = do
  str <- getContents
  case anaXUpdates str of
    Left e -> fail e
    Right cs -> mapM_ print cs

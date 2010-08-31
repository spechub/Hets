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
import Posixutil.ChildProcess
import Util.Computation
import Control.Concurrent

main :: IO ()
main = do
  p <- newChildProcess "isabelle" [arguments ["tty", "-l", "HOL"]]
  sendMsg p ""
  forkIO $ forever $ readMsg p >>= putStrLn
  return ()

import Posixutil.ChildProcess
import Util.Computation
import Control.Concurrent

main :: IO ()
main = do
  p <- newChildProcess "isabelle" [arguments ["tty", "-l", "HOL"]]
  sendMsg p ""
  forkIO $ forever $ readMsg p >>= putStrLn
  return ()

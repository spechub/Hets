import Common.XUpdate
import Control.Monad.Error

main :: IO ()
main = do
  str <- getContents
  case anaXUpdates str of
    Left e -> fail e
    Right cs -> mapM_ print cs

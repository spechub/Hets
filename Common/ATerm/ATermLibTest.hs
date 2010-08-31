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
import System
import ATerm.ReadWrite
import ATerm.SimpPretty

main :: IO ()
main = do args <- getArgs
          mapM_ testATC args

testATC :: FilePath -> IO ()
testATC fp = do str <- readFile fp
                let att = readATerm str
                putStrLn ("Reading File "++fp++" ...")
                let fp' = fp++".ttttt"
                putStrLn ("Writing File "++fp'++" ...")
                writeFileSDoc fp' (writeSharedATermSDoc att)

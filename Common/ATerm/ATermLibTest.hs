module Main where

import System
import Common.ATerm.ReadWrite
import Common.SimpPretty

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

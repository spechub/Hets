module PLpatt.Parse_PLpatt where

import PLpatt.AS_BASIC_PLpatt
import Text.ParserCombinators.Parsec
import Common.Result
import Control.Monad
import Haskell.Wrapper
import qualified Data.Text as Tx

parsemmt :: String -> IO (Result Basic_spec)
parsemmt s = do
                     putStr $ "---->  input: " ++ 
                            s ++ "-------------\n"
                     let decls = map
                                 (Tx.unpack . Tx.strip . Tx.pack) 
                                 $ lines s
                     let dcls = Result [] (Just decls)
                     let bs = liftM (\x -> Basic_spec x) dcls
                     print bs
                     return bs

procLines :: String -> Result Basic_spec
procLines s = let 
                decls = map
                        (Tx.unpack . Tx.strip . Tx.pack) 
                        $ lines s
                dcls = Result [] (Just decls)
                bs = liftM (\x -> Basic_spec x) dcls
                in
                bs
            

parse1 :: GenParser Char st Basic_spec
parse1 = do
    s <- hStuff
    let x = procLines s
    resultToMonad "MMT parser" x

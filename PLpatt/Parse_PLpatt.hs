module PLpatt.Parse_PLpatt where

--import Data.Maybe
import PLpatt.AS_BASIC_PLpatt
import Text.ParserCombinators.Parsec
import Common.Result
--import PLpatt.Tools
import System.IO.Unsafe
{-
import System.IO
import System.IO.Temp
import System.Process
-}
import Control.Monad
import Haskell.Wrapper
import qualified Data.Text as Tx

import Debug.Trace
--import MMT.Hets2mmt

{-
parseFile :: String -> IO Basic_spec
parseFile fname = do
      decls <- XML.parse fname
      let mres = map (fromJust . maybeResult) decls
      let dcs = map (fromJust . decl_from_pt) mres
      return $ Basic_spec dcs

parse :: CharParser st Basic_spec
parse = do
    let bspc = unsafePerformIO $ parseFile ""
    return bspc
-}

parsemmt :: String -> IO (Result Basic_spec)
parsemmt s = do
                     putStr $ "---->  input: " ++ 
                            s ++ "-------------\n"
                     -- drop the whitespace at the beginning of lines
                     let decls = map
                                 (Tx.unpack . Tx.strip . Tx.pack) 
                                 $ lines s
                     let dcls = Result [] (Just decls)
--                     putStr $ "decls: " ++ show dcls
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
                trace (show bs) bs
            

parse1 :: GenParser Char st Basic_spec
parse1 = do
    s <- hStuff
    let x = procLines s
    trace "returning Res Basic_spec" $ resultToMonad "MMT parser" x

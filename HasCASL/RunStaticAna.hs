
{- HetCATS/HasCASL/RunStaticAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse and call static analysis
-}


module RunStaticAna where

import AsToLe
import Lexer((<<))
import ParseItem
import Parsec
import ParsecError
import Result
import MonadState
import FiniteMap
import TypeInference

ana :: String -> State Env ()
ana s =   do e <- get
	     case parse (basicSpec << eof) "" s of
	       Left err -> writeMsg e (Error (showErrorMessages 
					      "or" "unknown parse error" 
                        "expecting" "unexpected" "end of input"
                       (errorMessages err)) (let p = errorPos err in 
					    (sourceLine p, sourceColumn p)))
	       Right x -> anaBasicSpec x

runAna :: String -> Env
runAna s = snd $ (runState (ana s)) initialEnv

printEnv :: Env -> IO ()
printEnv e = putStrLn $ showEnv e "" 
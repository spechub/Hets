
{- HetCATS/HasCASL/RunStaticAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse and call static analysis
-}


module RunStaticAna where

import Le
import AsToLe
import Lexer((<<))
import ParseItem
import Parsec
import ParsecError
import Result
import MonadState
import Pretty
import PrettyPrint
import PrintLe
import GlobalAnnotationsFunctions

ana :: String -> State Env ()
ana s =   do e <- get
	     case parse (basicSpec << eof) "" s of
	       Left err -> appendDiags [Diag Error (showErrorMessages 
					      "or" "unknown parse error" 
                        "expecting" "unexpected" "end of input"
                       (errorMessages err)) (let p = errorPos err in 
					    (sourceLine p, sourceColumn p))]
	       Right x -> anaBasicSpec x

runAna :: String -> Env
runAna s = snd $ (runState (ana s)) initialEnv

printEnv :: Env -> IO ()
printEnv e = putStrLn $ render $ printText0 emptyGlobalAnnos e 

main = readFile "B1.casl" >>= printEnv . runAna

module Reduce.Reduce_Interface where

import System.Directory
import System.Exit
import System.IO
import System.Process
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import Reduce.AS_BASIC_Reduce

type Session = (Handle,Handle)

-- | connects to the CAS, prepares the streams and sets initial options
connectCAS :: IO (Handle, Handle, Handle, ProcessHandle)
connectCAS = do 
  putStr "Connecting CAS.."
  (inp,out,err,pid) <-runInteractiveCommand "/home/dodi/import/reduce/reduce-algebra/trunk/bin/redcsl -w"
  hSetBuffering out NoBuffering
  hSetBuffering inp LineBuffering
  hPutStrLn inp "off nat;"
  hGetLine out
  hGetLine out
  hGetLine out
  putStrLn "done"
  return (inp,out,err,pid)
  
-- | closes the connection to the CAS
disconnectCAS :: (Handle,Handle)->IO()
disconnectCAS (inp,out) = do 
  hPutStrLn inp "quit;"
  return ()

 
-- | reads characters from the specified output until the next result is complete,
-- | indicated by $ when using the maxima mode off nat;
getNextResultOutput :: Handle->IO String
getNextResultOutput out = do
  b <- hIsEOF out
  if b then return [] else do
                        c <- hGetChar out
                        if c=='$' then return [] else do
                                                   r <- getNextResultOutput out
                                                   return (c:r)

procSimpleCmd :: (Handle,Handle)-> String -> IO String
casfactorExp (inp,out) s = do
  hPutStrLn inp s
  getNextResultOutput out

-- | factors a given expression over the reals
casfactorExp :: (Handle,Handle) -> EXPRESSION -> IO String 
casfactorExp (inp,out) exp = procSimpleCmd (inp,out) "factorize(a*a+b*b+2*a*b);"

-- | solves a single equation over the reals
cassolve :: (Handle,Handle)-> String -> IO String
casfactorExp (inp,out) exp = procSimpleCmd (inp,out) "factorize(a*a+b*b+2*a*b);"

-- | solves a list of equations 
-- solven

-- | simplifies a given expression over the reals   
cassimplify :: (Handle,Handle)-> String -> IO String
cassimplify (inp,out) exp = procSimpleCmd (inp,out) "factorize(a*a+b*b+2*a*b);"

-- | computes the remainder of a division
casremainder :: (Handle,Handle)-> String -> IO String
casremainder (inp,out) exp = procSimpleCmd (inp,out) "remainder((x+y)*(x+2*y),x+3*y);"

-- | computes the gcd of a division
casgcd :: (Handle,Handle)-> String -> IO String
casgcd (inp,out) exp = procSimpleCmd (inp,out) "gcd(f(x)+g(x)-l1-l2,f(x)-l1);"

-- | integrates the given expression
casint :: (Handle,Handle)-> String -> IO String
casint (inp,out) exp = procSimpleCmd (inp,out) "int(log(x),x);"

-- | performs quantifier elimination of a given expression
casqelim :: (Handle,Handle)-> String -> IO String
casqelim (inp,out) exp = procSimpleCmd (inp,out) "qelim(all(x, ex(y, x2+xy+b>0 and x+ay2+b<=0)))"
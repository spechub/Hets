module Reduce.Reduce_Interface where
import System.IO
import System.Process
import Reduce.AS_BASIC_Reduce
import Common.Id


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
disconnectCAS (inp,_) = do 
  hPutStrLn inp "quit;"
  putStrLn "CAS disconnected"
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

exportExps :: [EXPRESSION] -> String
exportExps [] = ""
exportExps (e1:e2:e3) = exportExp e1 ++ "," ++ (exportExps (e2:e3))
exportExps (e1:[]) = exportExp e1

-- | those operators declared as infix in Reduce
infixOps :: [String] 
infixOps = ["+","-","/","**","^","=","*"]

exportExp :: EXPRESSION -> String
exportExp (Var token) = tokStr token
exportExp (Op s [e1,e2] _) = if (elem s infixOps) then "(" ++ (exportExp e1) ++ s ++ (exportExp e2) ++ ")" 
                              else s++"("++(exportExp e1)++","++(exportExp e2)++")"
exportExp (Op s exps _) = s++"("++ (exportExps exps) ++ ")"
exportExp (List exps _) = "{" ++ (exportExps exps) ++ "}"
exportExp (Int i _) = show i
exportExp (Double d _) = show d

exportReduce :: CMD -> String
exportReduce (Cmd "simplify" exps) = exportExp $ head exps
exportReduce (Cmd cmd exps) = cmd ++ "(" ++ (exportExps exps) ++ ")"

procCmd :: (Handle,Handle) -> CMD -> IO [EXPRESSION]
procCmd (inp,out) cmd = case cmdstring of 
                          "simplify" -> cassimplify (inp,out) cmd
                          "remainder" -> casremainder (inp,out) cmd
                          "casgcd" -> casgcd (inp,out) cmd
                          "casint" -> casint (inp,out) cmd
                          "qelim" -> casqelim (inp,out) cmd
                          "factor" -> casfactorExp (inp,out) cmd
                          "solve" -> cassolve(inp,out) cmd
                          _ -> error "Command not supported"
                          where (Cmd cmdstring _) = cmd

procString :: (Handle,Handle)-> String -> IO [EXPRESSION]
procString (inp,out) s = do
  putStrLn $ "Send CAS cmd " ++ s
  hPutStrLn inp s
  res <- getNextResultOutput out
  putStrLn $ "Result is " ++ res
  return []


-- | factors a given expression over the reals
casfactorExp :: (Handle,Handle) -> CMD -> IO [EXPRESSION] 
casfactorExp (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | solves a single equation over the reals
cassolve :: (Handle,Handle)-> CMD-> IO [EXPRESSION]
cassolve (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | solves a list of equations 
-- solven

-- | simplifies a given expression over the reals   
cassimplify :: (Handle,Handle)-> CMD -> IO [EXPRESSION]
cassimplify (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | computes the remainder of a division
casremainder :: (Handle,Handle)-> CMD -> IO [EXPRESSION]
casremainder (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | computes the gcd of a division
casgcd :: (Handle,Handle)-> CMD -> IO [EXPRESSION]
casgcd (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | integrates the given expression
casint :: (Handle,Handle)-> CMD -> IO [EXPRESSION]
casint (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"

-- | performs quantifier elimination of a given expression
casqelim :: (Handle,Handle)-> CMD -> IO [EXPRESSION]
casqelim (inp,out) cmd = procString (inp,out) $ (exportReduce cmd) ++ ";"
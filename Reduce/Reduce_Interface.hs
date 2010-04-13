module Reduce.Reduce_Interface where
import System.IO
import System.Process
import Reduce.AS_BASIC_Reduce
import Reduce.Parse_AS_Basic
import Common.Id
import Logic.Prover
import Common.AS_Annotation
import Data.Time (midnight)
import Common.Utils (getEnvDef)

type Session = (Handle,Handle)

-- | returns the name of the reduce prover
reduceS :: String
reduceS = "Reduce"

-- | returns a basic proof status for conjecture with name n where [EXPRESSION] represents the proof tree
openReduceProofStatus :: String -> [EXPRESSION] -> ProofStatus [EXPRESSION]
openReduceProofStatus n prooftree = openProofStatus n reduceS prooftree


closedReduceProofStatus :: Ord pt => String -- ^ name of the goal
                -> pt -> ProofStatus pt
closedReduceProofStatus goalname proof_tree = 
    ProofStatus
    { goalName = goalname
    , goalStatus = Proved True
    , usedAxioms = []
    , usedProver = reduceS
    , proofTree = proof_tree
    , usedTime = midnight
    , tacticScript = TacticScript "" }

-- | connects to the CAS, prepares the streams and sets initial options
connectCAS :: IO (Handle, Handle, Handle, ProcessHandle)
connectCAS = do 
  putStr "Connecting CAS.."
  reducecmdline <- getEnvDef "HETS_REDUCE" "redcsl"
  (inp,out,err,pid) <-runInteractiveCommand $ reducecmdline ++ " -w"
  hSetBuffering out NoBuffering
  hSetBuffering inp LineBuffering
  hPutStrLn inp "off nat;"
  hPutStrLn inp "load redlog;"
  hPutStrLn inp "rlset reals;"
  hGetLine out
  hGetLine out
  hGetLine out
  hGetLine out
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
infixOps = ["+","-","/","**","^","=","*","and", "impl", "or"]

exportExp :: EXPRESSION -> String
exportExp (Var token) = tokStr token
exportExp (Op s [e1,e2] _) = if (elem s infixOps) then "(" ++ (exportExp e1) ++ s ++ (exportExp e2) ++ ")" 
                              else s++"("++(exportExp e1)++","++(exportExp e2)++")"
exportExp (Op s exps _) = s++"("++ (exportExps exps) ++ ")"
exportExp (List exps _) = "{" ++ (exportExps exps) ++ "}"
exportExp (Int i _) = show i
exportExp (Double d _) = show d

exportReduce :: Named CMD -> String
exportReduce namedcmd = case (sentence namedcmd) of 
                          (Cmd "simplify" exps) -> exportExp $ head exps
                          (Cmd cmd exps) ->  cmd ++ "(" ++ (exportExps exps) ++ ")"

procCmd :: (Handle,Handle) -> (Named CMD) -> IO (ProofStatus [EXPRESSION])
procCmd (inp,out) cmd = case cmdstring of 
                                 "simplify" -> cassimplify (inp,out) cmd
                                 "divide" -> casremainder (inp,out) cmd
                                 "rlqe" -> casqelim (inp,out) cmd
                                 "factorize" -> casfactorExp (inp,out) cmd
                                 "int" -> casint (inp,out) cmd
                                 "solve" -> cassolve(inp,out) cmd
                                 _ -> error "Command not supported"
    where (Cmd cmdstring _) = (sentence cmd)

-- | removes the newlines 4: from the beginning of the string
skipReduceLineNr :: String -> String
skipReduceLineNr s = dropWhile (\x -> elem x [' ','\n']) $ tail $ dropWhile (\x -> not (x==':')) s

-- | sends the given string to the CAS, reads the result and tries to parse it. 
procString :: (Handle,Handle)-> String -> String -> IO (ProofStatus [EXPRESSION])
procString (inp,out) axname s = do
  putStrLn $ "Send CAS cmd " ++ s
  hPutStrLn inp s
  res <- getNextResultOutput out
  putStrLn $ "Result is " ++ res
  putStrLn $ "Parsing of --" ++(skipReduceLineNr res)++ "-- yields " ++ show (parseResult (skipReduceLineNr res))
  case (parseResult (skipReduceLineNr res)) of
    Just e -> return $ closedReduceProofStatus axname [e]
    Nothing -> return $ openReduceProofStatus axname []


-- | factors a given expression over the reals
casfactorExp :: (Handle,Handle) -> Named CMD -> IO (ProofStatus [EXPRESSION])
casfactorExp (inp,out) cmd = procString (inp,out) (senAttr cmd) $ exportReduce cmd ++ ";"

-- | generates the lemma for cmd with result ProofStatus
exportLemmaFactor :: Named CMD -> (ProofStatus [EXPRESSION]) -> [EXPRESSION]
exportLemmaFactor namedcmd ps = [(Op "=" [exps!!0,(proofTree ps)!!0] nullRange)]
                           where (Cmd _ exps) = (sentence namedcmd)
                                 

-- | solves a single equation over the reals
cassolve :: (Handle,Handle)-> Named CMD-> IO (ProofStatus [EXPRESSION])
cassolve (inp,out) cmd = procString (inp,out) (senAttr cmd) $ (exportReduce cmd) ++ ";"

-- | solves a list of equations 
-- solven

-- | simplifies a given expression over the reals   
cassimplify :: (Handle,Handle)-> Named CMD -> IO (ProofStatus [EXPRESSION])
cassimplify (inp,out) cmd = procString (inp,out) (senAttr cmd)  $ (exportReduce cmd) ++ ";"

-- | computes the remainder of a division
casremainder :: (Handle,Handle)-> Named CMD -> IO (ProofStatus [EXPRESSION])
casremainder (inp,out) cmd = do
  divres <- procString (inp,out) (senAttr cmd) $ (exportReduce (makeNamed (senAttr cmd) (Cmd "divide" args))) ++ ";"
  return divres
         where (Cmd _ args)  = (sentence cmd)

-- | computes the gcd of a division
casgcd :: (Handle,Handle)-> Named CMD -> IO (ProofStatus [EXPRESSION])
casgcd (inp,out) cmd = procString (inp,out) (senAttr cmd) $ (exportReduce cmd) ++ ";"

-- | integrates the given expression
casint :: (Handle,Handle)-> Named CMD -> IO (ProofStatus [EXPRESSION])
casint (inp,out) cmd = procString (inp,out) (senAttr cmd) $ (exportReduce cmd) ++ ";"

-- | performs quantifier elimination of a given expression
casqelim :: (Handle,Handle)-> Named CMD -> IO (ProofStatus [EXPRESSION])
casqelim (inp,out) cmd = procString (inp,out) (senAttr cmd) $ (exportReduce cmd) ++ ";"


casDeclareOperators :: (Handle,Handle) -> [EXPRESSION] -> IO ()
casDeclareOperators (inp,out) varlist = do
  hPutStrLn inp $ "operator " ++ (exportExps varlist) ++ ";"
  hGetLine out
  return ()
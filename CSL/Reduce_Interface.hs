{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  interface to Reduce CAS
Copyright   :  (c) Dominik Dietrich, DFKI Bremen, 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Dominik.Dietrich@dfki.de
Stability   :  provisional
Portability :  non-portable (uses type-expression in class instances)

Interface for Reduce CAS system.
-}

module CSL.Reduce_Interface where

import Common.AS_Annotation
import Common.Id
import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef)

import Logic.Prover

import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic
import CSL.Lemma_Export

import Control.Monad (replicateM_)
import Data.Time (midnight)
import Data.Maybe (maybeToList)
import Data.List (intercalate)
import qualified Data.Map as Map

import System.IO
import System.Process

-- ----------------------------------------------------------------------
-- * Connection handling
-- ----------------------------------------------------------------------

-- | A session is a process connection
class Session a where
    outp :: a -> Handle
    inp :: a -> Handle
    err :: a -> Maybe Handle
    err = const Nothing
    proch :: a -> Maybe ProcessHandle
    proch = const Nothing

-- | The simplest session
instance Session (Handle, Handle) where
    inp = fst
    outp = snd

-- | Better use this session to properly close the connection
instance Session (Handle, Handle, ProcessHandle) where
    inp (x, _, _) = x
    outp (_, x, _) = x
    proch (_, _, x) = Just x


-- | Left String is success, Right String is failure
lookupRedShellCmd :: IO (Either String String)
lookupRedShellCmd  = do
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  let f = if noProg then Right else Left
  return $ f reducecmd


-- | connects to the CAS, prepares the streams and sets initial options
connectCAS :: String -> IO (Handle, Handle, Handle, ProcessHandle)
connectCAS reducecmd = do
    putStrLn "succeeded"
    (inpt, out, errh, pid) <- runInteractiveCommand $ reducecmd ++ " -w"
    hSetBuffering out NoBuffering
    hSetBuffering inpt LineBuffering
    hPutStrLn inpt "off nat;"
    hPutStrLn inpt "load redlog;"
    hPutStrLn inpt "rlset reals;"
    -- read 7 lines 
    replicateM_ 7 $ hGetLine out
    putStrLn "done"
    return (inpt, out, errh, pid)

-- | closes the connection to the CAS
disconnectCAS :: Session a => a -> IO ()
disconnectCAS s = do
  hPutStrLn (inp s) "quit;"
  case proch s of
    Nothing -> return ()

    -- this is always better, because it closes also the shell-process,
    -- hence use a Session-variant with ProcessHandle!
    Just ph -> waitForProcess ph >> return ()
  putStrLn "CAS disconnected"
  return ()

sendToReduce :: Session a => a -> String -> IO ()
sendToReduce sess s = do
  hPutStrLn (inp sess) s
  
-- ----------------------------------------------------------------------
-- * Prover specific
-- ----------------------------------------------------------------------

-- | returns the name of the reduce prover
reduceS :: String
reduceS = "Reduce"

{- | returns a basic proof status for conjecture with name n
  where [EXPRESSION] represents the proof tree. -}
openReduceProofStatus :: String -> [EXPRESSION] -> ProofStatus [EXPRESSION]
openReduceProofStatus n = openProofStatus n reduceS

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

{-
For Quantifier Elimination:

off nat; -- pretty-printing switch
load redlog;
rlset reals;

rlqe(exp...);
-}


-- ----------------------------------------------------------------------
-- * Reduce Pretty Printing
-- ----------------------------------------------------------------------

exportExps :: [EXPRESSION] -> String
exportExps l = intercalate "," $ map exportExp l


-- | those operators declared as infix in Reduce
infixOps :: [String]
infixOps = [ "+", "-", "/", "**", "^", "=", "<=", ">=", "<", ">", "*", "and"
           , "impl", "or"]

-- | exports an expression to Reduce format
exportExp :: EXPRESSION -> String
exportExp (Var token) = tokStr token
exportExp (Op s _ exps@[e1, e2] _) 
    | elem s infixOps = concat ["(", exportExp e1, s, exportExp e2, ")"]
    | otherwise       = concat [s, "(", exportExps exps, ")"]
exportExp (Op s _ [] _) = s
exportExp (Op s _ exps _) = concat [s, "(", exportExps exps, ")"]
exportExp (List exps _) = "{" ++ exportExps exps ++ "}"
exportExp (Int i _) = show i
exportExp (Double d _) = show d
exportExp (Interval l r _) =  concat [ "[", show l, ",", show r, "]" ]
--exportExp e = error $ "exportExp: expression not supported: " ++ show e

-- | exports command to Reduce Format
exportReduce :: Named CMD -> String
exportReduce namedcmd = case sentence namedcmd of
  Cmd "simplify" exps -> exportExp $ head exps
  Cmd "ask" exps -> exportExp $ head exps
  Cmd cmd exps -> cmd ++ "(" ++ exportExps exps ++ ")"
  _ -> error "exportReduce: not implemented for this case" -- TODO: implement


-- ----------------------------------------------------------------------
-- * Reduce Parsing
-- ----------------------------------------------------------------------

-- | removes the newlines 4: from the beginning of the string
skipReduceLineNr :: String -> String
skipReduceLineNr s = dropWhile (`elem` " \n") $ tail
                     $ dropWhile (/= ':') s

-- | try to get an EXPRESSION from a Reduce string
redOutputToExpression :: String -> Maybe EXPRESSION
redOutputToExpression = parseResult . skipReduceLineNr


-- ----------------------------------------------------------------------
-- * Reduce Commands
-- ----------------------------------------------------------------------


cslReduceDefaultMapping :: [(String, String)]
cslReduceDefaultMapping =
    let idmapping = map (\ x -> (x, x))
    in ("^", "**") :
         (idmapping $ Map.keys $ Map.delete "^" $ Map.delete "**" operatorInfo)

{- | reads characters from the specified output until the next result is
  complete, indicated by $ when using the maxima mode off nat; -}
getNextResultOutput :: Handle -> IO String
getNextResultOutput out = do
  b <- hIsEOF out
  if b then return "" else do
                        c <- hGetChar out
                        if c == '$' then return [] else do
                                                   r <- getNextResultOutput out
                                                   return (c : r)


procCmd :: Session a => a -> Named CMD
        -> IO (ProofStatus [EXPRESSION], [(Named CMD, ProofStatus [EXPRESSION])])
procCmd sess cmd = case cmdstring of
                     "simplify" -> cassimplify sess cmd
                     "ask" -> casask sess cmd
                     "divide" -> casremainder sess cmd
                     "rlqe" -> casqelim sess cmd
                     "factorize" -> casfactorExp sess cmd
                     "int" -> casint sess cmd
                     "solve" -> cassolve sess cmd
                     _ -> error "Command not supported"
    where Cmd cmdstring _ = sentence cmd

-- | sends the given string to the CAS, reads the result and tries to parse it.
evalString :: Session a => a -> String -> IO [EXPRESSION]
evalString sess s = do
  putStrLn $ "Send CAS cmd " ++ s
  hPutStrLn (inp sess) s
  res <- getNextResultOutput (outp sess)
  putStrLn $ "Result is " ++ res
  putStrLn $ "Parsing of --" ++ skipReduceLineNr res ++ "-- yields "
    ++ show (redOutputToExpression res)
  return $ maybeToList $ redOutputToExpression res

-- | wrap evalString into a ProofStatus
procString :: Session a => a -> String -> String -> IO (ProofStatus [EXPRESSION])
procString h axname s = do
  res <- evalString h s
  let f = if null res then openReduceProofStatus else closedReduceProofStatus
  return $ f axname res

-- | factors a given expression over the reals
casfactorExp :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
casfactorExp sess cmd =
  do
    proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
    return (proofstatus,[exportLemmaFactor cmd proofstatus])

-- | solves a single equation over the reals
cassolve :: Session a => a -> Named CMD -> IO (ProofStatus [EXPRESSION],[(Named CMD, ProofStatus [EXPRESSION])])
cassolve sess cmd =
  do 
    proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
    return (proofstatus,[])
    



-- | simplifies a given expression over the reals
cassimplify :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
cassimplify sess cmd = do
  proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
  return (proofstatus,[exportLemmaSimplify cmd proofstatus])




-- | asks value of a given expression 
casask :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
casask sess cmd = do
  proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
  return (proofstatus,[exportLemmaAsk cmd proofstatus])


-- | computes the remainder of a division
casremainder :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
casremainder sess cmd =
  do
    proofstatus <- procString sess (senAttr cmd) $ exportReduce (makeNamed (senAttr cmd) (Cmd "divide" args)) ++ ";" 
    return (proofstatus,[exportLemmaRemainder cmd proofstatus])
  where Cmd _ args = sentence cmd

-- | integrates the given expression
casint :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
casint sess cmd =
  do
    proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
    return (proofstatus,[exportLemmaInt cmd proofstatus])

-- | performs quantifier elimination of a given expression
casqelim :: Session a => a -> Named CMD -> IO ((ProofStatus [EXPRESSION]),[(Named CMD, ProofStatus [EXPRESSION])])
casqelim sess cmd =
  do
    proofstatus <- procString sess (senAttr cmd) $ exportReduce cmd ++ ";"
    return (proofstatus,[exportLemmaQelim cmd proofstatus])


exportLemmaQelim :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaQelim namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)

-- | declares an operator, such that it can used infix/prefix in CAS
casDeclareOperators :: Session a => a -> [EXPRESSION] -> IO ()
casDeclareOperators sess varlist = do
  hPutStrLn (inp sess) $ "operator " ++ exportExps varlist ++ ";"
  hGetLine (outp sess)
  return ()

-- | declares an equation x := exp 
casDeclareEquation :: Session a => a -> CMD -> IO ()
casDeclareEquation sess (Cmd s exps) = 
  if s == ":=" then 
    do
      putStrLn $ (exportExp (exps !! 0)) ++ ":=" ++  (exportExp (exps !! 1))
      hPutStrLn (inp sess) $ (exportExp (exps !! 0))
                    ++ ":=" ++  (exportExp (exps !! 1)) ++ ";"
      res <- getNextResultOutput (outp sess)
      putStrLn $ "Declaration Result: " ++ res
      return ()
   else error "Expression is not an equation"

casDeclareEquation _ _ =
    error "casDeclareEquation: not implemented for this case" -- TODO: implement


-- ----------------------------------------------------------------------
-- * Reduce Lemma Export
-- ----------------------------------------------------------------------

-- | generates the lemma for cmd with result ProofStatus
exportLemmaFactor :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaFactor namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)

exportLemmaSolve :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaSolve namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)

exportLemmaSimplify :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaSimplify namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)

exportLemmaAsk :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaAsk namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)

exportLemmaRemainder :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaRemainder namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)


exportLemmaInt :: Named CMD -> ProofStatus [EXPRESSION] -> (Named CMD, ProofStatus [EXPRESSION])
exportLemmaInt namedcmd ps =
  ((makeNamed lemmaname lemma), closedReduceProofStatus lemmaname [(Op "Proof" [] [] nullRange)])
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, head (proofTree ps)]
            lemmaname = (ganame namedcmd)


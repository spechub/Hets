{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Reduce instance for the CalculationSystem class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Reduce as CalculationSystem
-}

module CSL.ReduceInterpreter where

import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef)

import CSL.Reduce_Interface (evalString, exportExp, connectCAS, disconnectCAS)
import CSL.Parse_AS_Basic (mkOp)
import CSL.AS_BASIC_CSL (EXPRESSION)
import CSL.Interpreter

import Data.Maybe
import System.IO (Handle)

-- * Reduce Calculator Instance

data ReduceInterpreter = ReduceInterpreter { inh :: Handle
                                           , outh ::Handle }

instance CalculationSystem IO ReduceInterpreter where
    assign  = redAssign
    clookup = redClookup
    eval = redEval
    names = error "ReduceInterpreter as CS: names are unsupported"

initReduce :: IO ReduceInterpreter
initReduce = do
  putStr "Connecting CAS.."
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  error $ "Could not find reduce under " ++ reducecmd
{-
  if noProg
  then error $ "Could not find reduce under " ++ reducecmd
  else do
    (inp, out, _, _) <- connectCAS reducecmd
    return $ ReduceInterpreter { inh = inp, outh = out }
-}

exitReduce :: ReduceInterpreter -> IO ()
exitReduce r = disconnectCAS (inh r, outh r)

redAssign :: ReduceInterpreter -> String -> EXPRESSION -> IO ReduceInterpreter
redAssign r n e = do
  evalRedString r $ concat [n, ":=", exportExp e, ";"]
  return r

redClookup :: ReduceInterpreter -> String -> IO (Maybe EXPRESSION)
redClookup r n = do
  [e] <- evalRedString r $ n ++ ";"
  if e == mkOp n [] then return Nothing else return $ Just e

redEval :: EXPRESSION -> ReduceInterpreter -> IO EXPRESSION
redEval e r = do
  el <- evalRedString r $ exportExp e ++ ";"
  if null el then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated" else return $ head el


evalRedString :: ReduceInterpreter -> String -> IO [EXPRESSION]
evalRedString r = evalString (inh r, outh r)


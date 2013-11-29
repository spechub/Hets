{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeSynonymInstances
  , UndecidableInstances, OverlappingInstances, MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Reduce instance for the AssignmentStore class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (various glasgow extensions)

Reduce as AssignmentStore
-}

module CSL.ReduceInterpreter where

import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef, trimLeft)
import Common.IOS
import Common.ResultT

import CSL.Reduce_Interface ( evalString, exportExp, connectCAS, disconnectCAS
                            , lookupRedShellCmd, Session (..), cslReduceDefaultMapping)
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic (parseExpression)
import CSL.Transformation
import CSL.Interpreter

-- the process communication interface
import qualified Interfaces.Process as PC

import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Control.Monad.State (MonadState (..))

import Data.Maybe
import System.IO (Handle)
import System.Process (ProcessHandle)
import System.Exit (ExitCode)

import Prelude hiding (lookup)

{- ----------------------------------------------------------------------
Reduce Calculator Instances
---------------------------------------------------------------------- -}

data ReduceInterpreter = ReduceInterpreter { inh :: Handle
                                           , outh :: Handle
                                           , ph :: ProcessHandle
                                           , varcounter :: Int }

-- | ReduceInterpreter with Translator based on the CommandState
data RITrans = RITrans { getBMap :: BMap
                       , getRI :: PC.CommandState }


-- Types for two alternative reduce interpreter

-- Reds as (Red)uce (s)tandard interface
type RedsIO = ResultT (IOS ReduceInterpreter)

-- Redc as (Red)uce (c)ommand interface (it is built on CommandState)
type RedcIO = ResultT (IOS RITrans)

instance AssignmentStore RedsIO where
    assign = redAssign evalRedsString redsTransS return
    lookup = redLookup evalRedsString redsTransS
    eval = redEval evalRedsString return
    check = redCheck evalRedsString return
    names = error "ReduceInterpreter as CS: names are unsupported"

instance VarGen RedsIO where
    genVar = do
      s <- get
      let i = varcounter s
      put $ s { varcounter = i + 1 }
      return $ '?' : show i

instance AssignmentStore RedcIO where
    assign = redAssign evalRedcString redcTransS redcTransE
    lookup = redLookup evalRedcString redcTransS
    eval = redEval evalRedcString redcTransE
    check = redCheck evalRedcString redcTransE
    names = liftM (SMem . getBMap) get

instance VarGen RedcIO where
    genVar = do
      s <- get
      let i = newkey $ getBMap s
      put $ s { getBMap = (getBMap s) { newkey = i + 1 } }
      return $ '?' : show i

{- ----------------------------------------------------------------------
Reduce syntax functions
---------------------------------------------------------------------- -}

printAssignment :: String -> EXPRESSION -> String
printAssignment n e = concat [n, ":=", exportExp e, ";"]

printEvaluation :: EXPRESSION -> String
printEvaluation e = exportExp e ++ ";"

printLookup :: String -> String
printLookup n = n ++ ";"

{- As reduce does not support boolean expressions as first class citizens
we encode them in an if-stmt and transform the numeric response back. -}
printBooleanExpr :: EXPRESSION -> String
printBooleanExpr e = concat [ "on rounded;"
                            , " if "
                            , exportExp e, " then 1 else 0;"
                            , " off rounded;"
                            ]

getBooleanFromExpr :: EXPRESSION -> Bool
getBooleanFromExpr (Int 1 _) = True
getBooleanFromExpr (Int 0 _) = False
getBooleanFromExpr e =
    error $ "getBooleanFromExpr: can't translate expression to boolean: "
              ++ show e

{- ----------------------------------------------------------------------
Generic Communication Interface
---------------------------------------------------------------------- -}

{- |
   The generic interface abstracts over the concrete evaluation function
-}

redAssign :: (AssignmentStore s, MonadResult s) =>
             (String -> s [EXPRESSION])
          -> (ConstantName -> s String)
          -> (EXPRESSION -> s EXPRESSION)
          -> ConstantName -> AssDefinition -> s ()
redAssign ef trans transE n def =
  let e = getDefiniens def
      args = getArguments def
  in if null args then
         do
           e' <- transE e
           n' <- trans n
           ef $ printAssignment n' e'
           return ()
     else error $ "redAssign: functional assignments unsupported: " ++ show n

redLookup :: (AssignmentStore s, MonadResult s) =>
              (String -> s [EXPRESSION])
           -> (ConstantName -> s String)
           -> ConstantName -> s (Maybe EXPRESSION)
redLookup ef trans n = do
  n' <- trans n
  el <- ef $ printLookup n'
  return $ listToMaybe el
{- we don't want to return nothing on id-lookup: "x; --> x"
if e == mkOp n [] then return Nothing else return $ Just e -}

redEval :: (AssignmentStore s, MonadResult s) =>
           (String -> s [EXPRESSION])
        -> (EXPRESSION -> s EXPRESSION)
        -> EXPRESSION -> s EXPRESSION
redEval ef trans e = do
  e' <- trans e
  el <- ef $ printEvaluation e'
  if null el
   then error $ "redEval: expression " ++ show e' ++ " couldn't be evaluated"
   else return $ head el

redCheck :: (AssignmentStore s, MonadResult s) =>
            (String -> s [EXPRESSION])
         -> (EXPRESSION -> s EXPRESSION)
         -> EXPRESSION -> s Bool
redCheck ef trans e = do
  e' <- trans e
  el <- ef $ printBooleanExpr e'
  if null el
   then error $ "redCheck: expression " ++ show e' ++ " couldn't be evaluated"
   else return $ getBooleanFromExpr $ head el


{- ----------------------------------------------------------------------
The Standard Communication Interface
---------------------------------------------------------------------- -}

instance Session ReduceInterpreter where
    inp = inh
    outp = outh
    proch = Just . ph

redsTransS :: ConstantName -> RedsIO String
redsTransS = return . show

evalRedsString :: String -> RedsIO [EXPRESSION]
evalRedsString s = do
  r <- get
  liftIO $ evalString r s

redsInit :: IO ReduceInterpreter
redsInit = do
  putStr "Connecting CAS.."
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  if noProg
   then error $ "Could not find reduce under " ++ reducecmd
   else do
     (inpt, out, _, pid) <- connectCAS reducecmd
     return ReduceInterpreter
      { inh = inpt, outh = out, ph = pid, varcounter = 1 }

redsExit :: ReduceInterpreter -> IO ()
redsExit = disconnectCAS

{- ----------------------------------------------------------------------
An alternative Communication Interface
---------------------------------------------------------------------- -}


wrapCommand :: IOS PC.CommandState a -> IOS RITrans a
wrapCommand ios = do
  r <- get
  let map' x = r { getRI = x }
  stmap map' getRI ios

-- | A direct way to communicate with Reduce
redcDirect :: RITrans -> String -> IO String
redcDirect rit s = do
  (res, _) <- runIOS (getRI rit) (PC.call 0.5 s)
  return res

redcTransE :: EXPRESSION -> RedcIO EXPRESSION
redcTransE e = do
  r <- get
  let bm = getBMap r
      (bm', e') = translateExpr bm e
  put r { getBMap = bm' }
  return e'

redcTransS :: ConstantName -> RedcIO String
redcTransS s = do
  r <- get
  let bm = getBMap r
      (bm', s') = lookupOrInsert bm $ Left s
  put r { getBMap = bm' }
  return s'


evalRedcString :: String -> RedcIO [EXPRESSION]
evalRedcString s = do
  -- 0.09 seconds is a critical value for the accepted response time of Reduce
  res <- lift $ wrapCommand $ PC.call 0.5 s
  r <- get
  let bm = getBMap r
      trans = revtranslateExpr bm
  {- don't need to skip the reducelinenr here, because the Command-Interface
  cleans the outpipe before sending (hence removes the reduce line nr) -}
  return $ map trans $ maybeToList $ parseExpression operatorInfoMap
             $ trimLeft res

-- | init the reduce communication
redcInit :: Int -- ^ Verbosity level
         -> IO RITrans
redcInit v = do
  rc <- lookupRedShellCmd
  case rc of
    Left redcmd -> do
            cs <- PC.start redcmd v Nothing
            (_, cs') <- runIOS cs $ PC.send $ "off nat; load redlog; "
                        ++ "rlset reals; " -- on rounded; precision 30;"
            return RITrans { getBMap = initWithDefault cslReduceDefaultMapping
                           , getRI = cs' }
    _ -> error "Could not find reduce shell command!"

redcExit :: RITrans -> IO (Maybe ExitCode)
redcExit r = do
  (ec, _) <- runIOS (getRI r) $ PC.close $ Just "quit;"
  return ec

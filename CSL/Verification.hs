{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  $Header$
Description :  Generation of Verification Conditions
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

This module provides functionality for the generation of verification conditions
during program evaluation.
-}

module CSL.Verification where

--import qualified Data.Map as Map
import qualified Data.Set as Set
import CSL.Interpreter
import CSL.Transformation
import CSL.Analysis
import CSL.AS_BASIC_CSL

import System.IO
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.Error (MonadError (..))
import Control.Monad (when)

-- ----------------------------------------------------------------------
-- * Verification Conditions
-- ----------------------------------------------------------------------

{- Given an instantiated constant this data structure keeps 

* the value of this constant looked up in the assignment store

* for function constants its definition (looked up in the assignment store)

* the for this constant generated verification condition

data VCData = VCData
    { vcValue :: EXPRESSION
    , vcDef :: Maybe AssDefinition
    , vcCondition :: EXPRESSION
    }

type VCMap = Map.Map InstantiatedConstant VCData

-}


-- | Extra functionality of 'AssignmentStore's for VC generation
class AssignmentStore m => VCGenerator m where
    addVC :: EvalAtom -> EXPRESSION -> m ()

    -- these constants should be already part of the pure assignment store
    getDepGraph :: m (AssignmentDepGraph ())
    updateConstant :: ConstantName -> AssDefinition -> m ()

getVCPremises :: (Ord a) => AssignmentDepGraph a -- ^ 'DepGraph' for lookup
              -> EXPRESSION -- ^ generate premise for this term
              -> [EXPRESSION]
getVCPremises adg e =
    let scl = Set.map SimpleConstant $ setOfUserDefined e
        f (sc, depGrAnno) = mkVCPrem sc $ annoDef depGrAnno
    in map f $ Set.toList $ upperUntilRefl (const $ const False) adg scl

mkVCPrem :: ConstantName -> AssDefinition -> EXPRESSION
mkVCPrem n def
    | null args = toExp ("=", n, e)
    | otherwise = f args
    where e = getDefiniens def
          args = getArguments def
          f (x:l) = g x $ f l
          f _ = toExp ("=", toExp(n, map mkVar args), e)
          g v b = toExp ("all", mkVar v, b)

mkVC :: ConstantName 
     -> AssDefinition
     -> EXPRESSION -- ^ the evaluated term for the constant
     -> [EXPRESSION] -- ^ a list of premises from assignment graph
     -> EXPRESSION
mkVC _ def evalE prl = 
    let prem = foldl f (head prl) $ tail prl
        f a b = toExp ("and", a, b)
        conc = toExp ("=", getDefiniens def, evalE)
    in if null prl then conc else toExp ("impl", prem, conc)

mkBoolVC :: EXPRESSION -- ^ the Boolean term
         -> Bool -- ^ the evaluated Boolean term
         -> [EXPRESSION] -- ^ a list of premises from assignment graph
         -> EXPRESSION
mkBoolVC e evalB prl = 
    let prem = foldl f (head prl) $ tail prl
        f a b = toExp ("and", a, b)
        conc = if evalB then e else toExp ("not", e)
    in if null prl then conc else toExp ("impl", prem, conc)

verifyingStepper :: (VCGenerator m, MonadIO m, MonadError ASError m) =>
                    m () -> EvalAtom -> m Bool
verifyingStepper prog x = do
  liftIO $ putStrLn $ "At step " ++ show (prettyEvalAtom x)
  liftIO $ putStrLn ""
  b <- evaluateAndVerify prog x
  let breakPred s = s == "q" || null s
  s <- readEvalPrintLoop stdin stdout "next>" breakPred
  when (s == "q") $ throwError $ ASError UserError "Quit Debugger" 
  return b

evaluateAndVerify :: (VCGenerator m) => m () -> EvalAtom -> m Bool
evaluateAndVerify _ ea@(AssAtom n def) = do
  adg <- getDepGraph
  let prl = getVCPremises adg $ getDefiniens def
  e <- assign n def
  addVC ea $ mkVC n def e prl
  -- update the depgraph in the assignment store
  updateConstant n $ updateDefinition e def
  return True

evaluateAndVerify _ ea@(CaseAtom e) = do
  adg <- getDepGraph
  let prl = getVCPremises adg e
  b <- check e
  addVC ea $ mkBoolVC e b prl
  return b

evaluateAndVerify prog ea@(RepeatAtom e) = do
  prog
  adg <- getDepGraph
  let prl = getVCPremises adg e
  b <- check e
  addVC ea $ mkBoolVC e b prl
  return b



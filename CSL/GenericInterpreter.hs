{-# LANGUAGE  FlexibleContexts #-}
{- |
Module      :  $Header$
Description :  Generic ASState functionality for AssignmentStores
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

Generic functionality for 'AssignmentStore's based on the 'ASState'
datastructure. Handles all the translation stuff between the EnCL specification
and the terms on the CAS side
(see the 'BMap' structure in the Interpreter module)
-}

module CSL.GenericInterpreter where


import CSL.AS_BASIC_CSL
import CSL.Interpreter

import Control.Monad.State.Class
import Control.Monad.Reader

-- ----------------------------------------------------------------------
-- * Generic Translation Interface
-- ----------------------------------------------------------------------

getBooleanFromExpr :: EXPRESSION -> Either String Bool
getBooleanFromExpr (Op (OpId OP_true) _ _ _) = Right True
getBooleanFromExpr (Op (OpId OP_false) _ _ _) = Right False
getBooleanFromExpr (Op (OpId OP_failure) _ _ _) = Left "AssignmentStore FAILURE"
getBooleanFromExpr e = Left $ "Cannot translate expression to boolean: "
                       ++ show e

transConstant :: MonadState (ASState s) as => ConstantName -> as String
transConstant s = do
  r <- get
  let bm = getBMap r
      (bm', s') = lookupOrInsert bm s
  put r { getBMap = bm' }
  return s'

lookupConstant :: MonadState (ASState s) as => ConstantName -> as (Maybe String)
lookupConstant s = do
  r <- get
  let bm = getBMap r
  return $ rolookup bm s

transExpr :: MonadState (ASState s) as => EXPRESSION -> as EXPRESSION
transExpr e = do
  r <- get
  let bm = getBMap r
      (bm', e') = translateExpr bm e
  put r { getBMap = bm' }
  return e'

transExprWithVars :: MonadState (ASState s) as =>
                     [String] -> EXPRESSION -> as ([String], EXPRESSION)
transExprWithVars vl e = do
  r <- get
  let bm = getBMap r
      args = translateArgVars bm vl
      (bm', e') = translateExprWithVars vl bm e
  put r { getBMap = bm' }
  return (args, e')


transDef :: MonadState (ASState s) as => AssDefinition -> as AssDefinition
transDef (FunDef l e) = liftM (uncurry FunDef) $ transExprWithVars l e
transDef (ConstDef e) = liftM ConstDef $ transExpr e

transAssignment :: (MonadState (ASState s) as) =>
                   (ConstantName, AssDefinition) -> as (String, AssDefinition)
transAssignment (c, a) = do
  n' <- transConstant c
  def' <- transDef a
  return (n', def')

revtransDefExpr :: MonadState (ASState s) as => AssDefinition -> EXPRESSION
             -> as EXPRESSION
revtransDefExpr def = revtransExpr $ getArguments def

revtransExpr :: MonadState (ASState s) as => [String] -> EXPRESSION
             -> as EXPRESSION
revtransExpr args e = do
  r <- get
  let bm = getBMap r
  return $ if null args then revtranslateExpr bm e
           else revtranslateExprWithVars args bm e


-- ----------------------------------------------------------------------
-- * Generic AssignmentStore Methods
-- ----------------------------------------------------------------------

genAssign :: ( MonadState (ASState s) as) =>
             (String -> AssDefinition -> as EXPRESSION)
          -> ConstantName -> AssDefinition -> as EXPRESSION
genAssign ef n def =
    transAssignment (n, def) >>= uncurry ef >>= revtransDefExpr def

genAssigns :: (MonadState (ASState s) as) =>
             ([(String, AssDefinition)] -> as a)
           -> [(ConstantName, AssDefinition)] -> as a
genAssigns ef l = mapM transAssignment l >>= ef

genLookup :: (MonadState (ASState s) as) =>
             (String -> as EXPRESSION)
           -> ConstantName -> as (Maybe EXPRESSION)
genLookup ef n = do
  mN <- lookupConstant n
  case mN of
    Just n' ->
        ef n' >>= liftM Just . revtransExpr []
    _ -> return Nothing

genEval :: (MonadState (ASState s) as) =>
             (EXPRESSION -> as EXPRESSION)
           -> EXPRESSION -> as EXPRESSION
genEval ef e = transExpr e >>= ef >>= revtransExpr []

genCheck :: (MonadState (ASState s) as) =>
             (EXPRESSION -> as EXPRESSION)
           -> EXPRESSION -> as (Either String Bool)
genCheck ef e = transExpr e >>= liftM getBooleanFromExpr . ef


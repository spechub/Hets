{-# LANGUAGE  FlexibleContexts, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Generic ASState functionality for AssignmentStores
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

Generic functionality for 'AssignmentStore's based on the 'ASState'
datastructure.
-}

module CSL.GenericInterpreter where


import CSL.AS_BASIC_CSL
import CSL.Interpreter

import Control.Monad.State.Class
import Control.Monad.Reader

import Data.Maybe

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

revtransExpr :: MonadState (ASState s) as => AssDefinition -> EXPRESSION
             -> as EXPRESSION
revtransExpr def e = do
  r <- get
  let bm = getBMap r
      args = getArguments def
  return $ if null args then revtranslateExpr bm e
           else revtranslateExprWithVars args bm e


-- ----------------------------------------------------------------------
-- * Generic AssignmentStore Methods
-- ----------------------------------------------------------------------

genAssign' :: ( MonadState (ASState s) as) =>
             (String -> AssDefinition -> as (Maybe EXPRESSION))
                 -> ConstantName -> AssDefinition -> as (Maybe EXPRESSION)
genAssign' ef n def = do
  n' <- transConstant n
  def' <- transDef def
  mE <- ef n' def'
  case mE of
    Just e' -> liftM Just $ revtransExpr def e'
    _ -> return Nothing

genAssign :: ( MonadState (ASState s) as) =>
             (String -> AssDefinition -> as EXPRESSION)
          -> ConstantName -> AssDefinition -> as EXPRESSION
genAssign ef n def = let ef' c a = liftM Just $ ef c a
                     in liftM fromJust $ genAssign' ef' n def

genAssigns :: ( MonadState (ASState s) as) =>
             (String -> AssDefinition -> as ())
           -> [(ConstantName, AssDefinition)] -> as ()
genAssigns ef = let ef' c a = ef c a >> return Nothing
                in mapM_ $ (uncurry $ genAssign' ef')


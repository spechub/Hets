{-# LANGUAGE  FlexibleContexts, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Mathematica instance for the AssignmentStore class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

Mathematica as AssignmentStore based on the Mathlink interface
-}

module CSL.MathematicaInterpreter where

import Common.Id
import Common.Doc
import Common.DocUtils

import Common.MathLink


import CSL.AS_BASIC_CSL
import CSL.Interpreter
import CSL.Verification
import CSL.Analysis


import Control.Monad
--import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Control.Monad.Error
import Control.Monad.State

import Data.List hiding (lookup)
import qualified Data.Set as Set
import Data.Maybe
import System.IO


import Prelude hiding (lookup)



-- ----------------------------------------------------------------------
-- * Mathematica Types and Instances
-- ----------------------------------------------------------------------

-- | MathematicaInterpreter with Translator based on the MathLink interface
type MathState = ASState String

-- Mathematica interface, built on MathLink
type MathematicaIO = ErrorT ASError (StateT MathState ML)

instance AssignmentStore MathematicaIO where
    assign = error "AssignmentStore MathematicaIO"
    lookup = error "AssignmentStore MathematicaIO"
    eval = error "AssignmentStore MathematicaIO"
    evalRaw = error "AssignmentStore MathematicaIO"

    names = get >>= return . SMem . getBMap
    getUndefinedConstants e = do
      adg <- gets depGraph
      let g = isNothing . depGraphLookup adg
      return $ Set.filter g $ Set.map SimpleConstant $ setOfUserDefined e
      
    genNewKey = do
      mit <- get
      let (bm, i) = genKey $ getBMap mit
      put mit { getBMap = bm }
      return i

    getDepGraph = gets depGraph
    updateConstant n def =
        let f gr = updateGraph gr n
                   $ DepGraphAnno { annoDef = def
                                  , annoVal = () } 
            mf mit = mit { depGraph = f $ depGraph mit }
        in modify mf

instance VCGenerator MathematicaIO where
    addVC ea e = do
      let
          s = show
              $ (text "Verification condition for" <+> pretty ea <> text ":")
                    $++$ printExpForVC e
      vcHdl <- liftM (fromMaybe stdout) $ gets vericondOut
      liftIO $ hPutStrLn vcHdl s where
               

instance StepDebugger MathematicaIO where
    setDebugMode b = modify mf where mf mit = mit { debugMode = b }
    getDebugMode = gets debugMode

instance SymbolicEvaluator MathematicaIO where
    setSymbolicMode b = modify mf where mf mit = mit { symbolicMode = b }
    getSymbolicMode = gets symbolicMode

instance MessagePrinter MathematicaIO where
    printMessage = liftIO . putStrLn

-- ----------------------------------------------------------------------
-- * Mathematica syntax functions
-- ----------------------------------------------------------------------

mmShowOPNAME :: OPNAME -> String
mmShowOPNAME x =
    case x of
      OP_plus -> "Plus"
      OP_mult -> "Times"
      OP_pow -> "Power"
      OP_div -> "Divide"


      OP_neq -> "Unequal"
      OP_lt -> "Less"
      OP_leq -> "LessEqual"
      OP_eq -> "Equal"
      OP_gt -> "Greater"
      OP_geq -> "GreaterEqual"

      OP_sqrt -> "Sqrt"
      OP_abs -> "Abs"
      OP_sign -> "Sign"

      OP_max -> "Max"
      OP_min -> "Min"

      OP_cos -> "Cos"
      OP_sin -> "Sin"
      OP_tan -> "Tan"
      OP_Pi -> "Pi"

      OP_and -> "And"
      OP_not -> "Not"
      OP_or -> "Or"
      OP_impl -> "Implies"
      OP_false -> "False"
      OP_true -> "True"


      -- these functions have to be defined in a package
      OP_minus -> "Minus"
      OP_neg -> "Negate"

      OP_fthrt -> "fthrt"

      OP_maxloc -> "maxloc"
      OP_minloc -> "minloc"

      OP_reldist -> "reldist"
      OP_reldistLe -> "reldistLe"

      OP_undef -> "undef"
      OP_failure -> "fail"
      _ -> showOPNAME x

mmShowOPID :: OPID -> String
mmShowOPID (OpId x) = mmShowOPNAME x
mmShowOPID (OpUser (SimpleConstant s)) = s
mmShowOPID _ = error "mmShowOpId: unsupported constant"


-- | opInfoMap for mathematica's prdefined symbols
mathematicaOpInfoMap :: OpInfoMap
mathematicaOpInfoMap = getOpInfoMap (mmShowOPNAME . opname) operatorInfo


sendExpressionString :: String -> ML ()
sendExpressionString s = do
  mlPutFunction' "ToExpression" 1
  mlPutString s
  return ()

sendExpression :: EXPRESSION -> ML ()
sendExpression e =
  case e of
   Var token -> mlPutSymbol (tokStr token) >> return ()
   Op oi _ [] _ -> mlPutSymbol (mmShowOPID oi) >> return ()
   Op oi _ exps _ ->
       mlPutFunction' (mmShowOPID oi) (length exps) >> mapM_ sendExpression exps
   -- Integers are sent as strings, because the interface supports only machine
   -- integers not arbitrary sized integers.
   --   Int i _ -> mlPutInteger' i >> return ()
   Int i _ ->
       mlPutFunction' "ToExpression" 1 >> mlPutString (show i) >> return ()
   Double r _ -> mlPutReal' r >> return ()

   List _ _ -> error "sendExpression: List not supported"
   Interval _ _ _ -> error "sendExpression: Interval not supported"


receiveExpression :: ML EXPRESSION
receiveExpression =  do
  et <- mlGetNext
  let mkMLOp s args = mkAndAnalyzeOp mathematicaOpInfoMap s [] args nullRange
      pr | et == dfMLTKSYM = liftM (flip mkMLOp []) mlGetSymbol
         -- | et == dfMLTKINT = liftM (flip Int nullRange) mlGetInteger'
         | et == dfMLTKINT = liftM (flip Int nullRange . read) mlGetString
         | et == dfMLTKREAL = liftM (flip Double nullRange) mlGetReal'
         | et == dfMLTKFUNC =
             do
               len <- mlGetArgCount
               if len == 0 then mlProcError
                else do
                 -- the head is expected to be a symbol
                 et' <- mlGetNext
                 s <- if et' == dfMLTKSYM then mlGetSymbol else
                          error $ "receiveExpression: Expecting symbol at "
                                   ++ "function head, but got " ++ show et'
                 liftM (mkMLOp s) $ forM [1..len] $ const receiveExpression

         | et == dfMLTKERROR = mlProcError
         | otherwise = mlProcError
  pr

-- ----------------------------------------------------------------------
-- * Generic Communication Interface
-- ----------------------------------------------------------------------


-- ----------------------------------------------------------------------
-- * The Communication Interface
-- ----------------------------------------------------------------------


-- ----------------------------------------------------------------------
-- * The Mathematica system via MathLink
-- ----------------------------------------------------------------------



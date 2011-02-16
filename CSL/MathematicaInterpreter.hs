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
import CSL.GenericInterpreter


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
type MathState = ASState (MLState, Maybe FilePath)

-- Mathematica interface, built on MathLink
type MathematicaIO = ErrorT ASError (StateT MathState ML)

getMLState :: MathState -> MLState
getMLState = fst . getConnectInfo

getMLLogFile :: MathState -> Maybe FilePath
getMLLogFile = snd . getConnectInfo


liftML :: ML a -> MathematicaIO a
liftML = lift . lift


instance AssignmentStore MathematicaIO where
    assign  = genAssign mathematicaAssign
    assigns l = genAssigns mathematicaAssigns l >> return ()
    lookup = genLookup mathematicaLookup
    eval = genEval mathematicaEval
    check = mathematicaCheck
    names = get >>= return . SMem . getBMap
    evalRaw s = get >>= liftIO . mathematicaDirect s

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
-- * Mathematica syntax and special terms
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
   Int i _ -> mlPutInteger'' i >> return ()
   Double r _ -> mlPutReal' r >> return ()

   List _ _ -> error "sendExpression: List not supported"
   Interval _ _ _ -> error "sendExpression: Interval not supported"


receiveExpression :: ML EXPRESSION
receiveExpression =  do
  et <- mlGetNext
  let mkMLOp s args = mkAndAnalyzeOp mathematicaOpInfoMap s [] args nullRange
      pr | et == dfMLTKSYM = liftM (flip mkMLOp []) mlGetSymbol
         | et == dfMLTKINT = liftM (flip Int nullRange) mlGetInteger''
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


mathematicaSetTerm :: String -> AssDefinition -> EXPRESSION
mathematicaSetTerm s (ConstDef e) = mkOp "Set" [mkOp s [], e]
mathematicaSetTerm _ _ = error "mathematicaSetTerm: fundefs unsupported"

mathematicaListTerm :: [EXPRESSION] -> EXPRESSION
mathematicaListTerm = mkOp "List"

mathematicaSend :: EXPRESSION -> MathematicaIO ()
mathematicaSend e = liftML $ sendEvalPacket (sendExpression e) >> skipAnswer

-- ----------------------------------------------------------------------
-- * Methods for Mathematica 'AssignmentStore' Interface
-- ----------------------------------------------------------------------

mathematicaAssign :: String -> AssDefinition -> MathematicaIO EXPRESSION
mathematicaAssign s def = mathematicaEval $ mathematicaSetTerm s def

mathematicaAssigns :: [(String, AssDefinition)] -> MathematicaIO ()
mathematicaAssigns l = mathematicaSend $ mathematicaListTerm l'
    where l' = map (uncurry mathematicaSetTerm) l

mathematicaLookup :: String -> MathematicaIO EXPRESSION
mathematicaLookup s = mathematicaEval $ mkOp s []

mathematicaEval :: EXPRESSION -> MathematicaIO EXPRESSION
mathematicaEval e =
    liftML $ sendEvalPacket (sendExpression e) >> waitForAnswer
               >> receiveExpression

mathematicaCheck :: EXPRESSION -> MathematicaIO Bool
mathematicaCheck e = do
  eB <- genCheck mathematicaEval e
  case eB of
    Right b -> return b
    Left s ->
        throwError $ ASError CASError $
                   concat [ "mathematicaCheck: CAS error for expression "
                          , show e, "\n", s ]


-- ----------------------------------------------------------------------
-- * The Mathematica system via MathLink
-- ----------------------------------------------------------------------

-- TODO: implement the textpackage stuff
mathematicaDirect :: String -> MathState -> IO String
mathematicaDirect = error ""


withMathematica :: MathState -> MathematicaIO a -> IO (MathState, a)
withMathematica st mprog = do
  let stE = runErrorT mprog  -- (:: StateT MathState ML (Either ASError a))
      mlE = runStateT stE st -- (:: ML (Either ASError a, MathState))
  (eRes, st') <- withLink (getMLState st) (getMLLogFile st) mlE
  case eRes of
    Left err -> throwASError err
    Right res -> return (st', res)


-- | Init the Mathematica communication
mathematicaInit :: AssignmentDepGraph ()
          -> Int -- ^ Verbosity level
          -> Maybe FilePath -- ^ Log MathLink messages into this file
          -> Maybe String -- ^ Connection name
                          -- (launches a new kernel if not specified)
          -> IO MathState
mathematicaInit adg v mFp mN = do
  eMLSt <- openLink v mN
  case eMLSt of
    Left i ->
        error $ "mathematicaInit: MathLink connection failure " ++ show i
    Right mlSt ->
        return ASState { getBMap = initWithOpMap mathematicaOpInfoMap
                       , getConnectInfo = (mlSt, mFp)
                       , depGraph = adg
                       , debugMode = False
                       , symbolicMode = False
                       , verbosity = v
                       , vericondOut = Nothing
                       }

mathematicaExit :: MathState -> IO ()
mathematicaExit = closeLink . getMLState

{-

-- | Open connection to MathLink or return error code on failure
openLink :: Maybe String -- ^ Connection name
                         -- (launches a new kernel if not specified)
         -> IO (Either Int MLState)
-- | Run ML-program on an opened connection to MathLink
withLink :: MLState -- ^ MathLink connection
         -> Maybe FilePath -- ^ Log low level messages into this file (or STDOUT)
         -> ML a -- ^ The program to run
         -> IO a



type MathState = ASState MLState
type MathematicaIO = ErrorT ASError (StateT MathState ML)


runStateT ms $ runErrorT m

runErrorT :: ErrorT e m a -> m (Either e a)
runStateT :: StateT s m a -> s -> m (a, s)
-}

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

import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef, trimLeft)
import Common.Doc
import Common.DocUtils
import Common.IOS

import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic (parseExpression)
import CSL.Interpreter
import CSL.Transformation
import CSL.Verification
import CSL.Analysis

-- the process communication interface
import qualified Interfaces.Process as PC

import Control.Monad
--import Control.Monad.Trans (MonadTrans (..), MonadIO (..))
import Control.Monad.Error (ErrorT(..), MonadError (..))
import Control.Monad.State.Class
import Control.Monad.Reader

import Data.List hiding (lookup)
import qualified Data.Set as Set
import Data.Maybe
import System.Exit (ExitCode)
import System.IO

import Prelude hiding (lookup)


-- ----------------------------------------------------------------------
-- * Tests
-- ----------------------------------------------------------------------





-- ----------------------------------------------------------------------
-- * Mathematica Types and Instances
-- ----------------------------------------------------------------------

type ConnectInfo = (PC.CommandState, PC.DTime)

-- | MathematicaInterpreter with Translator based on the Mathlink interface
type MathState = ASState ConnectInfo

updateCS :: PC.CommandState -> ConnectInfo -> ConnectInfo
updateCS cs (_, dt) = (cs, dt)

updateDT :: PC.DTime -> ConnectInfo -> ConnectInfo
updateDT dt (cs, _) = (cs, dt)

getChannelTimeout :: MathState -> PC.DTime
getChannelTimeout = snd . getConnectInfo

setChannelTimeout :: PC.DTime -> MathState -> MathState
setChannelTimeout dt = fmap (updateDT dt)

getMI :: MathState -> PC.CommandState
getMI = fst . getConnectInfo

setMI :: PC.CommandState -> MathState -> MathState
setMI cs = fmap (updateCS cs)

-- Mathematica interface, built on CommandState
type MathematicaIO = ErrorT ASError (IOS MathState)

instance AssignmentStore MathematicaIO where
    assign  = mathematicaAssign (evalMathematicaString True) mathematicaTransS mathematicaTransVarE
    assigns =
        mathematicaAssigns (evalMathematicaString False []) mathematicaTransS mathematicaTransVarE
    lookup = mathematicaLookup (evalMathematicaString True []) mathematicaTransS
    eval = mathematicaEval (evalMathematicaString True []) mathematicaTransE
    check = mathematicaCheck (evalMathematicaString True []) mathematicaTransE
    names = get >>= return . SMem . getBMap
    evalRaw s = get >>= liftIO . flip (mathematicaDirect True) s

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
          --s = show $ printExpForVC e <> text ";"
          -- s = (++ "\n\n;\n\n") $ showRaw $ text "VC for" <+> pretty ea <> text ":" $++$ pretty e
--          vcHdl = stdout
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
-- * Mathematica Transformation Instances
-- ----------------------------------------------------------------------

-- TODO: Review the vargen facility and the cache-stuff in Transformation

-- | Variable generator instance for internal variables on the Hets-side,
-- in contrast to the newvar generation in lookupOrInsert of the BMap, which
-- generates variables for the Mathematica-side. We use nevertheless the same counter.
instance VarGen MathematicaIO where
    genVar = do
      s <- get
      let i = newkey $ getBMap s
      put $ s { getBMap = (getBMap s) { newkey = i + 1 } }
      return $ "?" ++ show i


-- ----------------------------------------------------------------------
-- * Mathematica syntax functions
-- ----------------------------------------------------------------------

printExp :: EXPRESSION -> String
printExp e = show $ runReader (printExpression e) mathematicaOpInfoNameMap
--printExp = exportExp
--printExp = show . pretty
-- :: ExpressionPrinter m => EXPRESSION -> m Doc



mathematicaOpInfoMap :: OpInfoMap
mathematicaOpInfoMap = operatorInfoMap

mathematicaOpInfoNameMap :: OpInfoNameMap
mathematicaOpInfoNameMap = operatorInfoNameMap

printAssignment :: String -> [String] -> EXPRESSION -> String
printAssignment n [] e = concat [n, ":= ", printExp e, ":", n, ";"]
printAssignment n l e = concat [ n, ":= proc", args, printExp e
                               , " end proc:", n, args, ";"]
    where args = concat [ "(", intercalate ", " l, ") " ]

printAssignmentWithEval :: String -> [String] -> EXPRESSION -> String
printAssignmentWithEval n [] e =
--    concat [n, ":= evalf(", printExp e, "):", n, " &+ 0", ";"]
--    concat [n, ":= evalf(", printExp e, "):", n, ";"]
    concat [n, ":= evalf(", printExp e, "):g(", n, ")", ";"]
printAssignmentWithEval n l e = concat [ n, ":= proc", args, printExp e
                                       , " end proc:", n, args, ";"]
    where args = concat [ "(", intercalate ", " l, ") " ]

printEvaluation :: EXPRESSION -> String
printEvaluation e = printExp e ++ ";"

printEvaluationWithEval :: EXPRESSION -> String
printEvaluationWithEval e = "evalf(" ++ printExp e ++ ");"

printLookup :: String -> String
printLookup n = n ++ ";"


{-
The evalf makes the decision much faster. As we verify the result formally
this should not be problematic in a formal context!


In the following context "is" gives up if we do not use "evalf":

x2 := cos(10+cos(10)/sin(10)+cos(10+cos(10)/sin(10))/sin(10+cos(10)/sin(10))
      + cos(10+cos(10)/sin(10)+cos(10+cos(10)/sin(10))/sin(10+cos(10)/sin(10)))
      / sin(10+cos(10)/sin(10)+cos(10+cos(10)/sin(10))/sin(10+cos(10)/sin(10))));
is(abs(x2)<1.0e-4);
-}
printBooleanExpr :: EXPRESSION -> String
printBooleanExpr e = concat [ "is(evalf(", printExp e, "));" ]

getBooleanFromExpr :: EXPRESSION -> Either String Bool
getBooleanFromExpr (Op (OpId OP_true) _ _ _) = Right True
getBooleanFromExpr (Op (OpId OP_false) _ _ _) = Right False
getBooleanFromExpr (Op (OpId OP_failure) _ _ _) = Left "Mathematica FAILURE"
getBooleanFromExpr e = Left $ "Cannot translate expression to boolean: "
                       ++ show e



-- The evalf is mandatory if we use the if-statement for encoding
{-

-- | As mathematica does not evaluate boolean expressions we encode them in an
-- if-stmt and transform the numeric response back.
printBooleanExpr :: EXPRESSION -> String
printBooleanExpr e = concat [ "if evalf("
                            , printExp e, ") then 1 else 0 fi;"
                            ]

getBooleanFromExpr :: EXPRESSION -> Bool
getBooleanFromExpr (Int 1 _) = True
getBooleanFromExpr (Int 0 _) = False
getBooleanFromExpr e =
    error $ "getBooleanFromExpr: can't translate expression to boolean: "
              ++ show e
-}

-- ----------------------------------------------------------------------
-- * Generic Communication Interface
-- ----------------------------------------------------------------------

{- |
   The generic interface abstracts over the concrete evaluation function
-}

mathematicaAssign :: (MonadError ASError s, MonadIO s, SymbolicEvaluator s) =>
               ([String] -> String -> s [EXPRESSION])
            -> (ConstantName -> s String)
            -> ([String] -> EXPRESSION -> s (EXPRESSION, [String]))
            -> ConstantName -> AssDefinition -> s EXPRESSION
mathematicaAssign ef trans transE n def = do
  let e = getDefiniens def
      args = getArguments def
  (e', args') <- transE args e
  n' <- trans n
  -- liftIO $ putStrLn $ show e'
  b <- getSymbolicMode
  let f = if b then printAssignment else printAssignmentWithEval
  el <- ef args $ f n' args' e'
--  el <- ef args $ printAssignment n' args' e'
  case el of
    [rhs] -> return rhs
    l -> throwError $ ASError InterfaceError $
         "mathematicaAssign: unparseable result for assignment of "
         ++ (show $ pretty n) ++ "\n" ++ (show $ pretty l)

mathematicaAssigns :: (AssignmentStore s) => (String -> s [EXPRESSION])
          -> (ConstantName -> s String)
          -> ([String] -> EXPRESSION -> s (EXPRESSION, [String]))
          -> [(ConstantName, AssDefinition)] -> s ()
mathematicaAssigns ef trans transE l =
    let f (n, def) = do
          let e = getDefiniens def
              args = getArguments def
          (e', args') <- transE args e
          n' <- trans n
          return $ printAssignment n' args' e'
    in mapM f l >>= ef . unlines >> return ()

mathematicaLookup :: (AssignmentStore s) => (String -> s [EXPRESSION])
           -> (ConstantName -> s String)
           -> ConstantName -> s (Maybe EXPRESSION)
mathematicaLookup ef trans n = do
  n' <- trans n
  el <- ef $ printLookup n'
  return $ listToMaybe el
-- we don't want to return nothing on id-lookup: "x; --> x"
--  if e == mkOp n [] then return Nothing else return $ Just e

mathematicaEval :: (MonadError ASError s, SymbolicEvaluator s) =>
             (String -> s [EXPRESSION])
        -> (EXPRESSION -> s EXPRESSION)
        -> EXPRESSION -> s EXPRESSION
mathematicaEval ef trans e = do
  e' <- trans e
  b <- getSymbolicMode
  let f = if b then printEvaluation else printEvaluationWithEval
  el <- ef $ f e'
  if null el
   then throwError $ ASError InterfaceError $
            "mathematicaEval: expression " ++ show e' ++ " couldn't be evaluated"
   else return $ head el

mathematicaCheck :: (MonadError ASError s, AssignmentStore s) =>
              (String -> s [EXPRESSION])
         -> (EXPRESSION -> s EXPRESSION)
         -> EXPRESSION -> s Bool
mathematicaCheck ef trans e = do
  e' <- trans e
  el <- ef $ printBooleanExpr e'
  if null el
   then throwError $ ASError CASError
            $ "mathematicaCheck: expression " ++ show e' ++ " could not be evaluated"
   else case getBooleanFromExpr $ head el of
          Right b -> return b
          Left s ->
              throwError
              $ ASError CASError $
                concat [ "mathematicaCheck: CAS error for expression "
                       , show e', "\n", s ]


-- ----------------------------------------------------------------------
-- * The Communication Interface
-- ----------------------------------------------------------------------


wrapCommand :: IOS PC.CommandState a -> IOS MathState a
wrapCommand ios = do
  r <- get
  let map' x = setMI x r
  stmap map' getMI ios

-- | A direct way to communicate with Mathematica
mathematicaDirect :: Bool -> MathState -> String -> IO String
mathematicaDirect b mit s = do
  (res, _) <- runIOS (getMI mit) $ PC.call (getChannelTimeout mit) s
  return $ if b then removeOutputComments res else res

mathematicaTransE :: EXPRESSION -> MathematicaIO EXPRESSION
mathematicaTransE e = do
  r <- get
  let bm = getBMap r
      (bm', e') = translateExpr bm e
  put r { getBMap = bm' }
  return e'

mathematicaTransVarE :: [String] -> EXPRESSION -> MathematicaIO (EXPRESSION, [String])
mathematicaTransVarE vl e = do
  r <- get
  let bm = getBMap r
      args = translateArgVars bm vl
      (bm', e') = translateExprWithVars vl bm e
  put r { getBMap = bm' }
  return (e', args)

mathematicaTransS :: ConstantName -> MathematicaIO String
mathematicaTransS s = do
  r <- get
  let bm = getBMap r
      (bm', s') = lookupOrInsert bm s
  --     outs = [ "lookingUp " ++ show s ++ " in "
  --            , show $ pretty bm, "{", show bm, "}" ]
  -- liftIO $ putStrLn $ unlines outs

  put r { getBMap = bm' }
  return s'


-- | Evaluate the given String as mathematica expression and
-- parse the result to an expression list.
evalMathematicaString :: Bool -- ^ Use parser
                -> [String] -- ^ Use this argument list for variable trafo
                -> String -> MathematicaIO [EXPRESSION]
evalMathematicaString b args s = do
  -- 0.09 seconds is a critical value for the accepted response time of Mathematica
  mit <- get
  res <- lift $ wrapCommand $ PC.call (getChannelTimeout mit) s
  let bm = getBMap mit
      trans = if null args then revtranslateExpr bm
              else revtranslateExprWithVars args bm
  -- when b $ liftIO $ putStrLn $ "evalMathematicaString:"
  -- when b $ liftIO $ putStrLn $ show $ maybeToList $ parseExpression mathematicaOpInfoMap $ trimLeft
  --          $ removeOutputComments res
  -- when b $ liftIO $ putStrLn $ show $ map trans $ maybeToList $ parseExpression mathematicaOpInfoMap $ trimLeft
  --          $ removeOutputComments res
  return $ if b
           then map trans $ maybeToList $ parseExpression mathematicaOpInfoMap
                    $ trimLeft $ removeOutputComments res
           else []

-- | init the mathematica communication
mathematicaInit :: AssignmentDepGraph ()
          -> Int -- ^ Verbosity level
          -> PC.DTime -- ^ timeout for response
          -> IO MathState
mathematicaInit adg v to = do
  rc <- lookupMathematicaShellCmd
  libpath <- getEnvDef "HETS_MATHEMATICALIB"
             $ error "mathematicaInit: Environment variable HETS_MATHEMATICALIB not set."
  case rc of
    Left mathematicacmd -> do
            cs <- PC.start (mathematicacmd ++ " -q") v
                  $ Just PC.defaultConfig { PC.startTimeout = 3 }
            (_, cs') <- runIOS cs $ PC.call 0.5
                        $ concat [ "interface(prettyprint=0); Digits := 10;"
                                 , "libname := \"", libpath, "\", libname;" ]
            return ASState { getBMap = initWithOpMap mathematicaOpInfoMap
                           , getConnectInfo = (cs', to)
                           , depGraph = adg
                           , debugMode = False
                           , symbolicMode = False
                           , vericondOut = Nothing
                           }
    _ -> error "Could not find mathematica shell command!"


-- | Loads a mathematica module such as intpakX or intCompare
mathematicaLoadModule :: MathState -> String -> IO String
mathematicaLoadModule rit s =
    fmap fst $ runIOS (getMI rit) (PC.call 0.5 $ "with(" ++ s ++ ");")


mathematicaExit :: MathState -> IO (Maybe ExitCode)
mathematicaExit mit = do
  (ec, _) <- runIOS (getMI mit) $ PC.close $ Just "quit;"
  return ec

execWithMathematica :: MathState -> MathematicaIO a -> IO (MathState, a)
execWithMathematica mit m = do
  let err s = error $ "execWithMathematica: " ++ s
  (res, mit') <- runIOS mit $ runErrorT m
  case res of
    Left s' -> err $ asErrorMsg s'
    Right x -> return (mit', x)

runWithMathematica :: AssignmentDepGraph () -> Int -- ^ Verbosity level
          -> PC.DTime -- ^ timeout for response
          -> [String] -> MathematicaIO a
          -> IO (MathState, a)
runWithMathematica adg i to l m = do
  mit <- mathematicaInit adg i to
  mapM_ (mathematicaLoadModule mit) l

  -- wraps an interval around the number
  let debugFun = "g := proc(v) z:=abs(Float(v,1-Digits)):[v-z, v+z] end;"
  runIOS (getMI mit) $ PC.call 0.3 debugFun
        
  execWithMathematica mit m

-- ----------------------------------------------------------------------
-- * The Mathematica system
-- ----------------------------------------------------------------------

-- | Left String is success, Right String is failure
lookupMathematicaShellCmd :: IO (Either String String)
lookupMathematicaShellCmd  = do
  cmd <- getEnvDef "HETS_MATHEMATICA" "mathematica"
  -- check that prog exists
  noProg <- missingExecutableInPath cmd
  let f = if noProg then Right else Left
  return $ f cmd

-- | Removes lines starting with ">"
removeOutputComments :: String -> String
removeOutputComments =
    filter (/= '\\') . concat . filter (not . isPrefixOf ">") . lines
 

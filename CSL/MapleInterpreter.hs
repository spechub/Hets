{-# LANGUAGE  FlexibleContexts, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Maple instance for the AssignmentStore class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

Maple as AssignmentStore
-}

module CSL.MapleInterpreter where

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
-- * Maple Calculator Instances
-- ----------------------------------------------------------------------

-- | MapleInterpreter with Translator based on the CommandState
data MITrans = MITrans { getBMap :: BMap
                       , getMI :: PC.CommandState
                       , depGraph :: AssignmentDepGraph ()
                       , debugMode :: Bool
                       , vericondOut :: Maybe Handle
                       , channelTimeout :: PC.DTime }


-- Maple interface, built on CommandState
type MapleIO = ErrorT ASError (IOS MITrans)

instance AssignmentStore MapleIO where
    assign  = mapleAssign (evalMapleString True) mapleTransS mapleTransVarE
    assigns =
        mapleAssigns (evalMapleString False []) mapleTransS mapleTransVarE
    lookup = mapleLookup (evalMapleString True []) mapleTransS
    eval = mapleEval (evalMapleString True []) mapleTransE
    check = mapleCheck (evalMapleString True []) mapleTransE
    names = get >>= return . SMem . getBMap
    evalRaw s = get >>= liftIO . flip (mapleDirect True) s

    getUndefinedConstants e = do
      adg <- gets depGraph
      let g = isNothing . depGraphLookup adg
      return $ Set.filter g $ Set.map SimpleConstant $ setOfUserDefined e
      
    genNewKey = do
      mit <- get
      let (bm, i) = genKey $ getBMap mit
      put mit { getBMap = bm }
      return i

instance VCGenerator MapleIO where
    getDepGraph = gets depGraph
    updateConstant n def =
        let f gr = updateGraph gr n
                   $ DepGraphAnno { annoDef = def
                                  , annoVal = () } 
            mf mit = mit { depGraph = f $ depGraph mit }
        in modify mf
        
    addVC ea e = do
      let
          -- s = show $ text "VC for" <+> pretty ea <> text ":" $++$ pretty e
          s = show $ pretty e <> text ";"
          -- s = (++ "\n\n;\n\n") $ showRaw $ text "VC for" <+> pretty ea <> text ":" $++$ pretty e
--          vcHdl = stdout
      vcHdl <- liftM (fromMaybe stdout) $ gets vericondOut
      liftIO $ hPutStrLn vcHdl s where
               

instance StepDebugger MapleIO where
    setDebugMode b = modify mf where mf mit = mit { debugMode = b }
    getDebugMode = gets debugMode

-- ----------------------------------------------------------------------
-- * Maple Transformation Instances
-- ----------------------------------------------------------------------

-- TODO: Review the vargen facility and the cache-stuff in Transformation

-- | Variable generator instance for internal variables on the Hets-side,
-- in contrast to the newvar generation in lookupOrInsert of the BMap, which
-- generates variables for the Maple-side. We use nevertheless the same counter.
instance VarGen MapleIO where
    genVar = do
      s <- get
      let i = newkey $ getBMap s
      put $ s { getBMap = (getBMap s) { newkey = i + 1 } }
      return $ "?" ++ show i


-- ----------------------------------------------------------------------
-- * Maple syntax functions
-- ----------------------------------------------------------------------

printExp :: EXPRESSION -> String
printExp e = show $ runReader (printExpression e) mapleOpInfoNameMap
--printExp = exportExp
--printExp = show . pretty
-- :: ExpressionPrinter m => EXPRESSION -> m Doc



mapleOpInfoMap :: OpInfoMap
mapleOpInfoMap = operatorInfoMap

mapleOpInfoNameMap :: OpInfoNameMap
mapleOpInfoNameMap = operatorInfoNameMap

-- TODO: The mapping should be OPNAME to OPNAME or we should remove the mapping
-- just adapt the opinfo-map for pretty printing for each CAS!
cslMapleDefaultMapping :: [(OPNAME, String)]
cslMapleDefaultMapping = 
    let idmapping = map (\ x -> (x, show x))
--        ampmapping = map (\ x -> (x, "&" ++ show x))
        possibleIntervalOps = [ OP_mult, OP_div, OP_plus, OP_minus, OP_neg
                              , OP_cos,  OP_sin, OP_tan, OP_sqrt, OP_abs
                              , OP_neq, OP_lt, OP_leq, OP_eq, OP_gt, OP_geq ]
        logicOps = [ OP_and, OP_or, OP_impl, OP_true, OP_false ]
        otherOps = [ OP_factor, OP_maxloc, OP_sign, OP_Pi, OP_min, OP_max
                   , OP_fthrt, OP_reldist, OP_reldistLe]
        specialOps = [(OP_pow, "^"), (OP_failure, "FAIL")]
--        specialOp = (OP_pow, "&**")
    in specialOps ++ idmapping logicOps ++ idmapping possibleIntervalOps
           ++ idmapping otherOps

printAssignment :: String -> [String] -> EXPRESSION -> String
printAssignment n [] e = concat [n, ":= ", printExp e, ":", n, ";"]
printAssignment n l e = concat [ n, ":= proc", args, printExp e
                               , " end proc:", n, args, ";"]
    where args = concat [ "(", intercalate ", " l, ") " ]

printEvaluation :: EXPRESSION -> String
printEvaluation e = printExp e ++ ";"

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
getBooleanFromExpr (Op (OpId OP_failure) _ _ _) = Left "Maple FAILURE"
getBooleanFromExpr e = Left $ "Cannot translate expression to boolean: "
                       ++ show e



-- The evalf is mandatory if we use the if-statement for encoding
{-

-- | As maple does not evaluate boolean expressions we encode them in an
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

mapleAssign :: (MonadError ASError s, AssignmentStore s, MonadIO s) =>
               ([String] -> String -> s [EXPRESSION])
            -> (ConstantName -> s String)
            -> ([String] -> EXPRESSION -> s (EXPRESSION, [String]))
            -> ConstantName -> AssDefinition -> s EXPRESSION
mapleAssign ef trans transE n def = do
  let e = getDefiniens def
      args = getArguments def
  (e', args') <- transE args e
  n' <- trans n
  -- liftIO $ putStrLn $ show e'
  el <- ef args $ printAssignment n' args' e'
  case el of
    [rhs] -> return rhs
    l -> throwError $ ASError InterfaceError $
         "mapleAssign: unparseable result for assignment of "
         ++ (show $ pretty n) ++ "\n" ++ (show $ pretty l)

mapleAssigns :: (AssignmentStore s) => (String -> s [EXPRESSION])
          -> (ConstantName -> s String)
          -> ([String] -> EXPRESSION -> s (EXPRESSION, [String]))
          -> [(ConstantName, AssDefinition)] -> s ()
mapleAssigns ef trans transE l =
    let f (n, def) = do
          let e = getDefiniens def
              args = getArguments def
          (e', args') <- transE args e
          n' <- trans n
          return $ printAssignment n' args' e'
    in mapM f l >>= ef . unlines >> return ()

mapleLookup :: (AssignmentStore s) => (String -> s [EXPRESSION])
           -> (ConstantName -> s String)
           -> ConstantName -> s (Maybe EXPRESSION)
mapleLookup ef trans n = do
  n' <- trans n
  el <- ef $ printLookup n'
  return $ listToMaybe el
-- we don't want to return nothing on id-lookup: "x; --> x"
--  if e == mkOp n [] then return Nothing else return $ Just e

mapleEval :: (MonadError ASError s, AssignmentStore s) =>
             (String -> s [EXPRESSION])
        -> (EXPRESSION -> s EXPRESSION)
        -> EXPRESSION -> s EXPRESSION
mapleEval ef trans e = do
  e' <- trans e
  el <- ef $ printEvaluation e'
  if null el
   then throwError $ ASError InterfaceError $
            "mapleEval: expression " ++ show e' ++ " couldn't be evaluated"
   else return $ head el

mapleCheck :: (MonadError ASError s, AssignmentStore s) =>
              (String -> s [EXPRESSION])
         -> (EXPRESSION -> s EXPRESSION)
         -> EXPRESSION -> s Bool
mapleCheck ef trans e = do
  e' <- trans e
  el <- ef $ printBooleanExpr e'
  if null el
   then throwError $ ASError CASError
            $ "mapleCheck: expression " ++ show e' ++ " could not be evaluated"
   else case getBooleanFromExpr $ head el of
          Right b -> return b
          Left s ->
              throwError
              $ ASError CASError $
                concat [ "mapleCheck: CAS error for expression "
                       , show e', "\n", s ]


-- ----------------------------------------------------------------------
-- * The Communication Interface
-- ----------------------------------------------------------------------


wrapCommand :: IOS PC.CommandState a -> IOS MITrans a
wrapCommand ios = do
  r <- get
  let map' x = r { getMI = x }
  stmap map' getMI  ios

-- | A direct way to communicate with Maple
mapleDirect :: Bool -> MITrans -> String -> IO String
mapleDirect b mit s = do
  (res, _) <- runIOS (getMI mit) $ PC.call (channelTimeout mit) s
  return $ if b then removeOutputComments res else res

mapleTransE :: EXPRESSION -> MapleIO EXPRESSION
mapleTransE e = do
  r <- get
  let bm = getBMap r
      (bm', e') = translateExpr bm e
  put r { getBMap = bm' }
  return e'

mapleTransVarE :: [String] -> EXPRESSION -> MapleIO (EXPRESSION, [String])
mapleTransVarE vl e = do
  r <- get
  let bm = getBMap r
      args = translateArgVars bm vl
      (bm', e') = translateExprWithVars vl bm e
  put r { getBMap = bm' }
  return (e', args)

mapleTransS :: ConstantName -> MapleIO String
mapleTransS s = do
  r <- get
  let bm = getBMap r
      (bm', s') = lookupOrInsert bm s
  --     outs = [ "lookingUp " ++ show s ++ " in "
  --            , show $ pretty bm, "{", show bm, "}" ]
  -- liftIO $ putStrLn $ unlines outs

  put r { getBMap = bm' }
  return s'


-- | Evaluate the given String as maple expression and
-- parse the result to an expression list.
evalMapleString :: Bool -- ^ Use parser
                -> [String] -- ^ Use this argument list for variable trafo
                -> String -> MapleIO [EXPRESSION]
evalMapleString b args s = do
  -- 0.09 seconds is a critical value for the accepted response time of Maple
  mit <- get
  res <- lift $ wrapCommand $ PC.call (channelTimeout mit) s
  let bm = getBMap mit
      trans = if null args then revtranslateExpr bm
              else revtranslateExprWithVars args bm
  -- when b $ liftIO $ putStrLn $ "evalMapleString:"
  -- when b $ liftIO $ putStrLn $ show $ maybeToList $ parseExpression mapleOpInfoMap $ trimLeft
  --          $ removeOutputComments res
  -- when b $ liftIO $ putStrLn $ show $ map trans $ maybeToList $ parseExpression mapleOpInfoMap $ trimLeft
  --          $ removeOutputComments res
  return $ if b
           then map trans $ maybeToList $ parseExpression mapleOpInfoMap
                    $ trimLeft $ removeOutputComments res
           else []

-- | init the maple communication
mapleInit :: AssignmentDepGraph ()
          -> Int -- ^ Verbosity level
          -> PC.DTime -- ^ timeout for response
          -> IO MITrans
mapleInit adg v to = do
  rc <- lookupMapleShellCmd
  libpath <- getEnvDef "HETS_MAPLELIB"
             $ error "mapleInit: Environment variable HETS_MAPLELIB not set."
  case rc of
    Left maplecmd -> do
            cs <- PC.start (maplecmd ++ " -q") v
                  $ Just PC.defaultConfig { PC.startTimeout = 3 }
            (_, cs') <- runIOS cs $ PC.call 0.5
                        $ concat [ "interface(prettyprint=0); Digits := 10;"
                                 , "libname := \"", libpath, "\", libname;" ]
            return MITrans { getBMap = initWithOpMap mapleOpInfoMap
                           , getMI = cs'
                           , depGraph = adg
                           , debugMode = False
                           , vericondOut = Nothing
                           , channelTimeout = to
                           }
    _ -> error "Could not find maple shell command!"


-- | Loads a maple module such as intpakX or intCompare
mapleLoadModule :: MITrans -> String -> IO String
mapleLoadModule rit s =
    fmap fst $ runIOS (getMI rit) (PC.call 0.5 $ "with(" ++ s ++ ");")


mapleExit :: MITrans -> IO (Maybe ExitCode)
mapleExit mit = do
  (ec, _) <- runIOS (getMI mit) $ PC.close $ Just "quit;"
  return ec

execWithMaple :: MITrans -> MapleIO a -> IO (MITrans, a)
execWithMaple mit m = do
  let err s = error $ "execWithMaple: " ++ s
  (res, mit') <- runIOS mit $ runErrorT m
  case res of
    Left s' -> err $ asErrorMsg s'
    Right x -> return (mit', x)

runWithMaple :: AssignmentDepGraph () -> Int
          -> PC.DTime -- ^ timeout for response
          -> [String] -> MapleIO a
          -> IO (MITrans, a)
runWithMaple adg i to l m = do
  mit <- mapleInit adg i to
  mapM_ (mapleLoadModule mit) l
  execWithMaple mit m

-- ----------------------------------------------------------------------
-- * The Maple system
-- ----------------------------------------------------------------------

-- | Left String is success, Right String is failure
lookupMapleShellCmd :: IO (Either String String)
lookupMapleShellCmd  = do
  cmd <- getEnvDef "HETS_MAPLE" "maple"
  -- check that prog exists
  noProg <- missingExecutableInPath cmd
  let f = if noProg then Right else Left
  return $ f cmd

-- | Removes lines starting with ">"
removeOutputComments :: String -> String
removeOutputComments =
    filter (/= '\\') . concat . filter (not . isPrefixOf ">") . lines
 
{- Some problems with the maximization in Maple:

> Maximize(-x^6+t*x^3-3, {t >= -1000, t <= 1000}, x=-2..0);     
Error, (in Optimization:-NLPSolve) no improved point could be found
> Maximize(-x^t*x^3-3, {t >= -1000, t <= 1000}, x=-2..0);  
Error, (in Optimization:-NLPSolve) complex value encountered


-- works better:
rhs(maximize(-(tan(x)-1/12)^2 -1, x=-1..1, location)[2,1,1,1]);
-}

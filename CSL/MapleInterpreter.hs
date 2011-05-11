{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Maple instance for the AssignmentStore class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Maple as AssignmentStore
-}

module CSL.MapleInterpreter where

import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef, trimLeft)
import Common.Doc
import Common.DocUtils
import Common.IOS

import CSL.AS_BASIC_CSL
import CSL.ASUtils
import CSL.Print_AS
import CSL.Parse_AS_Basic (parseExpression)
import CSL.Interpreter
import CSL.Verification
import CSL.DependencyGraph
import CSL.GenericInterpreter

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
-- * Maple Types and Instances
-- ----------------------------------------------------------------------

type ConnectInfo = (PC.CommandState, PC.DTime)

-- | MapleInterpreter with Translator based on the CommandState
type MITrans = ASState ConnectInfo

updateCS :: PC.CommandState -> ConnectInfo -> ConnectInfo
updateCS cs (_, dt) = (cs, dt)

updateDT :: PC.DTime -> ConnectInfo -> ConnectInfo
updateDT dt (cs, _) = (cs, dt)

getChannelTimeout :: MITrans -> PC.DTime
getChannelTimeout = snd . getConnectInfo

setChannelTimeout :: PC.DTime -> MITrans -> MITrans
setChannelTimeout dt = fmap (updateDT dt)

getMI :: MITrans -> PC.CommandState
getMI = fst . getConnectInfo

setMI :: PC.CommandState -> MITrans -> MITrans
setMI cs = fmap (updateCS cs)

-- Maple interface, built on CommandState
type MapleIO = ErrorT ASError (IOS MITrans)

instance AssignmentStore MapleIO where
    assign  = genAssign mapleAssignDirect
    assigns l = genAssigns mapleAssignsDirect l >> return ()
    lookup = genLookup mapleLookupDirect
    eval = genEval mapleEvalDirect
    check = mapleCheck
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

    getDepGraph = gets depGraph
    updateConstant n def =
        let f gr = updateGraph gr n
                   $ DepGraphAnno { annoDef = def
                                  , annoVal = () } 
            mf mit = mit { depGraph = f $ depGraph mit }
        in modify mf

instance VCGenerator MapleIO where
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

instance StepDebugger MapleIO where
    setDebugMode b = modify mf where mf mit = mit { debugMode = b }
    getDebugMode = gets debugMode

instance SymbolicEvaluator MapleIO where
    setSymbolicMode b = modify mf where mf mit = mit { symbolicMode = b }
    getSymbolicMode = gets symbolicMode

instance MessagePrinter MapleIO where
    printMessage = liftIO . putStrLn

-- ----------------------------------------------------------------------
-- * Maple syntax functions
-- ----------------------------------------------------------------------

data OfMaple a = OfMaple { mplValue :: a }

type MaplePrinter = Reader (OfMaple OpInfoNameMap)

instance ExpressionPrinter MaplePrinter where
    getOINM = asks mplValue
    printOpname = return . text . mplShowOPNAME

printMaplePretty :: (MaplePrinter Doc) -> Doc
printMaplePretty = flip runReader $ OfMaple mapleOpInfoNameMap

class MaplePretty a where
    mplPretty :: a -> Doc

instance MaplePretty EXPRESSION where
    mplPretty e = printMaplePretty $ printExpression e

instance MaplePretty AssDefinition where
    mplPretty def = printMaplePretty $ printAssDefinition def

instance MaplePretty String where
    mplPretty = text

instance (MaplePretty a, MaplePretty b) => MaplePretty [(a, b)] where
    mplPretty l = ppPairlist mplPretty mplPretty braces sepBySemis (<>) l


printExp :: EXPRESSION -> String
printExp = show . mplPretty


mplShowOPNAME :: OPNAME -> String
mplShowOPNAME OP_approx = "evalf"
mplShowOPNAME x = showOPNAME x

mapleOpInfoMap :: OpInfoMap
mapleOpInfoMap = operatorInfoMap

mapleBindInfoMap :: BindInfoMap
mapleBindInfoMap = operatorBindInfoMap

mapleOpInfoNameMap :: OpInfoNameMap
mapleOpInfoNameMap = operatorInfoNameMap

printAssignment :: String -> AssDefinition -> String
printAssignment n (ConstDef e) = concat [n, ":= ", printExp e, ":", n, ";"]
printAssignment n (FunDef l e) = concat [ n, ":= proc", args, printExp e
                                        , " end proc:", n, args, ";"]
    where args = concat [ "(", intercalate ", " l, ") " ]

printAssignmentWithEval :: String -> AssDefinition -> String
printAssignmentWithEval n (ConstDef e) =
--    concat [n, ":= evalf(", printExp e, "):", n, " &+ 0", ";"]
--    concat [n, ":= evalf(", printExp e, "):", n, ";"]
    concat [n, ":= evalf(", printExp e, "):g(", n, ")", ";"]
printAssignmentWithEval n (FunDef l e) = concat [ n, ":= proc", args, printExp e
                                                , " end proc:", n, args, ";"]
    where args = concat [ "(", intercalate ", " l, ") " ]

printEvaluation :: EXPRESSION -> String
printEvaluation e = printExp e ++ ";"

--printEvaluationWithEval :: EXPRESSION -> String
--printEvaluationWithEval e = "evalf(" ++ printExp e ++ ");"

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

-- The evalf is mandatory if we use the if-statement for encoding
{-

-- | As maple does not evaluate boolean expressions we encode them in an
-- if-stmt and transform the numeric response back.
printBooleanExpr :: EXPRESSION -> String
printBooleanExpr e = concat [ "if evalf("
                            , printExp e, ") then 1 else 0 fi;"
                            ]

-}

-- ----------------------------------------------------------------------
-- * Methods for Maple 'AssignmentStore' Interface
-- ----------------------------------------------------------------------

-- | Evaluate the given String as maple expression and
-- parse the result to an maybe expression. If the boolean flag is false
-- the result will not be parsed.
evalMapleString' :: Bool -- ^ Use parser
                -> String -- ^ the maple command to evaluate
                -> MapleIO (Maybe EXPRESSION)
evalMapleString' b s = do
  -- 0.09 seconds is a critical value for the accepted response time of Maple
  mit <- get
  res <- lift $ wrapCommand $ PC.call (getChannelTimeout mit) s
  return $ if b
           --    then parseExpression mapleOpInfoMap $ trimLeft $ removeOutputComments res
           then parseExpression (mapleOpInfoMap, mapleBindInfoMap) $ trimLeft res
           else Nothing

-- | Evaluate the given String as maple expression and skip the result
sendMapleString :: String -- ^ the maple command to evaluate
                -> MapleIO ()
sendMapleString s = evalMapleString' False s >> return ()

-- | Evaluate the given String as maple expression and
-- parse the result back to an expression.
evalMapleString :: String -- ^ an error message for the failure case
                -> String -- ^ the maple command to evaluate
                -> MapleIO EXPRESSION
evalMapleString msg s = do
  mE <- evalMapleString' True s
  case mE of
    Just e -> return e
    _ -> throwError $ ASError InterfaceError msg

mapleAssignDirect :: String -> AssDefinition -> MapleIO EXPRESSION
mapleAssignDirect n def = do
  sm <- getSymbolicMode
  let f = if sm then printAssignment else printAssignmentWithEval
      msg = "mapleAssignDirect: unparseable result for assignment of "
            ++ (show $ pretty n <+> pretty def)
  prettyInfo3 $ mplPretty [(n, def)]
  evalMapleString msg $ f n def

mapleAssignsDirect :: [(String, AssDefinition)] -> MapleIO ()
mapleAssignsDirect =
    sendMapleString . unlines . map (uncurry printAssignment)


mapleLookupDirect :: String -> MapleIO EXPRESSION
mapleLookupDirect n = evalMapleString msg $ printLookup n where
    msg = "mapleLookupDirect: unparseable result for lookup of " ++ n


mapleEvalDirect :: EXPRESSION -> MapleIO EXPRESSION
mapleEvalDirect e = do
--  b <- getSymbolicMode
  let -- f = if b then printEvaluation else printEvaluationWithEval
      msg = "mapleEvalDirect: unparseable result for evaluation of "
            ++ (show $ pretty e)
  evalMapleString msg $ printEvaluation e -- f e

mapleCheck :: EXPRESSION -> MapleIO Bool
mapleCheck e = do
  let msg = "mapleCheck: unparseable result for evaluation of "
            ++ (show $ pretty e)
  eB <- genCheck (evalMapleString msg . printBooleanExpr) e
  case eB of
    Right b -> return b
    Left s ->
        throwError $ ASError CASError $
                   concat [ "mapleCheck: CAS error for expression "
                          , show e, "\n", s ]

-- ----------------------------------------------------------------------
-- * The Communication Interface
-- ----------------------------------------------------------------------


wrapCommand :: IOS PC.CommandState a -> IOS MITrans a
wrapCommand ios = do
  r <- get
  let map' x = setMI x r
  stmap map' getMI ios

-- | A direct way to communicate with Maple
mapleDirect :: Bool -> MITrans -> String -> IO String
mapleDirect b mit s = do
  (res, _) <- runIOS (getMI mit) $ PC.call (getChannelTimeout mit) s
  return $ if b then removeOutputComments res else res

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
            return $ initASState (cs', to) mapleOpInfoMap adg v
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

runWithMaple :: AssignmentDepGraph () -> Int -- ^ Verbosity level
          -> PC.DTime -- ^ timeout for response
          -> [String] -> MapleIO a
          -> IO (MITrans, a)
runWithMaple adg i to l m = do
  mit <- mapleInit adg i to
  mapM_ (mapleLoadModule mit) l

  -- wraps an interval around the number
  let debugFun = "g := proc(v) z:=abs(Float(v,1-Digits)):[v-z, v+z] end;"
  runIOS (getMI mit) $ PC.call 0.3 debugFun
        
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

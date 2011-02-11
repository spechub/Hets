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

import Common.Doc
import Common.DocUtils

import Common.MathLink


import CSL.AS_BASIC_CSL
import CSL.Interpreter
import CSL.Verification
import CSL.Analysis


import Foreign.C.Types

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


-- ----------------------------------------------------------------------
-- * Generic Communication Interface
-- ----------------------------------------------------------------------


-- ----------------------------------------------------------------------
-- * The Communication Interface
-- ----------------------------------------------------------------------


-- ----------------------------------------------------------------------
-- * The Mathematica system via MathLink
-- ----------------------------------------------------------------------


-- ----------------------------------------------------------------------
-- * MathLink stuff
-- ----------------------------------------------------------------------



readAndPrintOutput :: ML ()
readAndPrintOutput = do
  exptype <- mlGetNext
  let pr | exptype == dfMLTKSYM = readAndPrintML "Symbol: " mlGetSymbol
         | exptype == dfMLTKSTR = readAndPrintML "String: " mlGetString
         | exptype == dfMLTKINT = readAndPrintML "Int: " mlGetInteger
         | exptype == dfMLTKREAL = readAndPrintML "Real: " mlGetReal
         | exptype == dfMLTKFUNC =
             do
               len <- mlGetArgCount
               if len == 0 then mlProcError
                else do
                 let f i = readAndPrintOutput
                           >> if i < len then userMessage ", " else return ()
                 readAndPrintOutput
                 userMessage "["
                 forM_ [1..len] f
                 userMessage "]"

         | exptype == dfMLTKERROR = userMessageLn "readAndPrintOutput-error" >> mlProcError
         | otherwise = userMessageLn ("readAndPrintOutput-error" ++ show exptype)
                       >> mlProcError
  pr



userMessage :: String -> ML ()
userMessage s = logMessage s >> liftIO (putStr s)

userMessageLn :: String -> ML ()
userMessageLn s = logMessageLn s >> liftIO (putStrLn s)


class MLShow a where
    mlshow :: a -> String

instance MLShow String where
    mlshow s = s

instance MLShow CDouble where
    mlshow = show

instance MLShow CInt where
    mlshow = show

readAndPrintML :: MLShow a => String -> ML a -> ML ()
readAndPrintML _ pr = pr >>= userMessage . mlshow


-- * Test functionality

sendPlus :: CInt -> CInt -> CInt -> ML ()
sendPlus i j k = do
  mlPutFunction "EvaluatePacket" 1
  mlPutFunction "Plus" 3
  mlPutInteger i
  mlPutInteger j
  mlPutInteger k
  mlEndPacket
  userMessageLn "Sent"


sendFormula :: CInt -> CInt -> CInt -> ML ()
sendFormula i j k = do
  mlPutFunction "EvaluatePacket" 1

  mlPutFunction "Plus" 2
  mlPutFunction "Times" 2
  mlPutInteger i
  mlPutInteger j
  mlPutFunction "Times" 3
  mlPutInteger k
  mlPutInteger k
  mlPutSymbol "xsymb"

  mlEndPacket

  userMessageLn "Sent"


-- ----------------------------------------------------------------------
-- * Tests
-- ----------------------------------------------------------------------

test :: [String] -> IO ()
test argv = do
  let (k, i, j) = (read $ argv!!0, read $ argv!!1, read $ argv!!2)
      mN = if length argv > 3 then Just $ argv!!3 else Nothing

--  liftIO (putStrLn $ "Sending " ++ show (i, j, k))

  -- Send Plus[i, j]
  eRes <- runLink (Just "/tmp/mlffi.txt") mN $
          forM_ [1 .. k] $ sendFormula i j >=>
                const (receivePacket >> readAndPrintOutput >> userMessageLn "")
  case eRes of
    Left eid -> putStrLn $ "Error " ++ show eid
    _ -> putStrLn $ "OK"


  
  

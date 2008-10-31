{- |
Module      :  $Header$
Description :  ConservativityChecker for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

THe QBF solver sKizzo is used for conservativity checking. This is the
code connecting it to Hets
-}

module Propositional.Conservativity
    (
     conserCheck
    )
    where

import Common.AS_Annotation
import Common.Result
import Common.Consistency
import qualified Data.Set as Set
import Common.Id
import System.Exit
import System.IO.Unsafe
import Control.Monad
import qualified Data.Map as Map
import Common.Id
import System.Cmd
import System.Directory
import Data.Time.Clock
import System.Process

-- Propositional Stuff
import Propositional.Sign
import Propositional.AS_BASIC_Propositional
import Propositional.Morphism
import Propositional.Prop2CNF
import Propositional.Conversions
import Propositional.Tools

proverName :: String
proverName = "sKizzo"

defOptions :: String
defOptions = "-timeout 60"

-- | Conservativity Check for Propositional Logic
conserCheck :: (Sign, [Named FORMULA])      -- ^ Initial sign and formulas
           -> Morphism                      -- ^ morhpism between specs
           -> [Named FORMULA]               -- ^ Formulas of extended spec
           -> Result (Maybe (ConsistencyStatus, [FORMULA]))
conserCheck (_, inSens) mor cSens=
    do
      let cForms  = getFormulas cSens
          inSig   =  source mor
          cSig    =  target mor
      inFormsM <- mapM (mapSentence mor) $ getFormulas inSens
      let checkForm =
              Implication
                 (Conjunction inFormsM nullRange)
                 (Conjunction cForms nullRange)
                 nullRange
      result <- unsafePerformIO $
                doConservCheck inSig cSig checkForm
      return result

-- | Extraction of needed formulas, removes all Axioms and Annotations
getFormulas :: [Named FORMULA] -> [FORMULA]
getFormulas sens = foldl (\out sen->
                                     out ++
                                     (
                                      if (isAxiom sen)
                                       then
                                           [sentence sen]
                                       else
                                           []
                                     )
                                ) [] sens

doConservCheck :: Sign       -- ^ Initial  Sign
               -> Sign       -- ^ Extended Sign
               -> FORMULA    -- ^ QBF Formula to Prove
               -> IO (Result (Maybe (ConsistencyStatus, [FORMULA])))
doConservCheck inSig exSig form =
    do
      (oSig , cnf) <- translateToCNF (exSig, [makeNamed "QBF Formula" form])
      if (length cnf /= 1)
       then
           fail "Translation error"
       else
           do
             let iMap = createSignMap oSig 1 Map.empty
                 iSym = items inSig
                 eSym = (items oSig) `Set.difference` iSym
             qdim <- showQDimacs iSym eSym iMap cnf
             res  <- runSKizzo qdim
             return (return (Just (res,[])))

-- | Printer for QDimacs Format
showQDimacs :: Set.Set Id               -- ^ Symbols of initial  Sign
            -> Set.Set Id               -- ^ New symbols of extended Sign
            -> Map.Map Token Integer    -- ^ Map of Symbols
            -> [Named FORMULA]          -- ^ Formulas to Translate
            -> IO String
showQDimacs inSym exSym sigMap forms =
    do
      let fforms  = concat $ map flatten $ map sentence forms
          numVars = Set.size inSym + Set.size exSym
      return $ "c Conservativity Problem Created by Hets \n" ++
             "p cnf " ++ show numVars ++ " " ++
             (show $ length fforms) ++ "\n" ++
             "a " ++ Set.fold
                      (\sym str ->
                           (show $ Map.findWithDefault 0 (head $
                              getSimpleId sym) sigMap) ++ " " ++  str
                      ) "" inSym ++ "0\n" ++
             "e " ++ Set.fold
                      (\sym str ->
                           (show $ Map.findWithDefault 0 (head $
                              getSimpleId sym) sigMap) ++ " " ++ str
                      ) "" exSym ++ "0\n" ++
             (\tflAxs ->
                  case tflAxs of
                    [] -> ""
                    _  -> "c Axioms\n" ++
                              (foldl (\sr xv -> sr ++
                                      mapClause xv sigMap) "" tflAxs)
             ) fforms

-- | gets simple Id
getSimpleId :: Id -> [Token]
getSimpleId (Id toks _ _) = toks

-- | Runs sKizzo that has to reside in your path
runSKizzo :: String                  -- ^ File in qdimacs syntax
          -> IO ConsistencyStatus
runSKizzo qd =
    do
      hasProgramm <- system ("which " ++  proverName
                             ++ " > /dev/null 2> /dev/null")
      case hasProgramm of
        ExitFailure _ ->
            do
              return $ Unknown (proverName ++ " not found in your $PATH$")
        ExitSuccess ->
            do
              tmp  <- getTemporaryDirectory
              time <- getCurrentTime
              let path = tmp ++ "/sKizzoTemp_" ++
                         (replaceBaddies $ show time) ++ ".qdimacs"
              writeFile path qd
              let command = proverName ++ " " ++ defOptions ++ " " ++ path
              (_,_,_,pid) <- runInteractiveCommand command
              exCode <- waitForProcess pid
              removeFile path
              case exCode of
                ExitFailure 10   -> return Conservative
                ExitFailure 20   -> return Inconsistent
                ExitFailure 30   -> return $ Unknown "Timeout"
                ExitFailure 40   -> return $ Unknown "Cannot solve"
                ExitFailure 250  -> return $ Unknown "Out of memory"
                ExitFailure 251  -> return $ Unknown "sKizzo crashed"
                ExitFailure 254  -> return $ Unknown "File not found"
                ExitFailure (-4) -> return $ Unknown "Parse error"
                ExitFailure (-5) -> return $ Unknown "sKizzo crashed"
                ExitFailure (-6) -> return $ Unknown "Out of memory"
                n                -> return $ Unknown $ "Unkown, exit was: " ++
                                    show n

-- | Helper to filter out problematic characters
replaceBaddies :: String -> String
replaceBaddies s = map (\x -> case x of
                               ' ' -> '_'
                               ':' -> '_'
                               y   -> y
                      ) s

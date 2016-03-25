{- |
Module      :  ./Propositional/Conservativity.hs
Description :  ConservativityChecker for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

THe QBF solver sKizzo is used for conservativity checking. This is the
code connecting it to Hets
-}

module Propositional.Conservativity (conserCheck) where

import Common.AS_Annotation
import Common.Consistency
import Common.Id
import Common.Result
import Common.Utils

import System.Directory
import System.Exit

import qualified Data.Map as Map
import qualified Data.Set as Set

-- Propositional Stuff
import Propositional.Sign
import Propositional.AS_BASIC_Propositional
import Propositional.Morphism
import Propositional.Conversions
import Propositional.Fold

proverName :: String
proverName = "sKizzo"

defOptions :: String
defOptions = "-timeout 60"

-- | Conservativity Check for Propositional Logic
conserCheck :: (Sign, [Named FORMULA])      -- ^ Initial sign and formulas
           -> Morphism                      -- ^ morhpism between specs
           -> [Named FORMULA]               -- ^ Formulas of extended spec
           -> IO (Result (Conservativity, [FORMULA]))
conserCheck (_, inSens) mor cForms = do
      let inSig = source mor
          cSig = target mor
      case mapM (mapSentence mor) $ getFormulas inSens of
        Result ds Nothing -> return $ Result ds Nothing
        Result _ (Just inFormsM) -> do
          let checkForm = Implication
                 (Conjunction inFormsM nullRange)
                 (Conjunction (map sentence cForms) nullRange)
                 nullRange
          doConservCheck inSig cSig checkForm

-- | Extraction of needed formulas, removes all Theorems and Annotations
getFormulas :: [Named FORMULA] -> [FORMULA]
getFormulas = map sentence . filter isAxiom

doConservCheck :: Sign       -- ^ Initial  Sign
               -> Sign       -- ^ Extended Sign
               -> FORMULA    -- ^ QBF Formula to Prove
               -> IO (Result (Conservativity, [FORMULA]))
doConservCheck inSig oSig form = do
             let iMap = createSignMap oSig 1 Map.empty
                 iSym = items inSig
                 eSym = items oSig `Set.difference` iSym
                 fs = getConj $ cnf form
                 qdim = showQDimacs iSym eSym iMap fs
             -- exclude the trivial case that makes sKizzo fail
             if null fs then return $ return (Cons, []) else do
               res <- runSKizzo qdim
               return $ return (res, [])

-- | Printer for QDimacs Format
showQDimacs :: Set.Set Id               -- ^ Symbols of initial  Sign
            -> Set.Set Id               -- ^ New symbols of extended Sign
            -> Map.Map Token Integer    -- ^ Map of Symbols
            -> [FORMULA]          -- ^ Formulas to Translate
            -> String
showQDimacs inSym exSym sigMap fforms =
      let numVars = Set.size inSym + Set.size exSym
          fct sym str = show (Map.findWithDefault 0 (id2SimpleId sym) sigMap)
                        ++ " " ++ str
      in "c Conservativity Problem Created by Hets \n" ++
             "p cnf " ++ show numVars ++ " " ++
             show (length fforms) ++ "\n" ++
             "a " ++ Set.fold fct "" inSym ++ "0\n" ++
             "e " ++ Set.fold fct "" exSym ++ "0\n" ++
             case fforms of
                    [] -> ""
                    _ -> "c Axioms\n" ++ concatMap (`mapClause` sigMap)
                          fforms

-- | Runs sKizzo that has to reside in your path
runSKizzo :: String                  -- ^ File in qdimacs syntax
          -> IO Conservativity
runSKizzo qd = do
              path <- getTempFile qd "sKizzoTemp.qdimacs"
              (exCode, out, err1) <- executeProcess proverName
                (words defOptions ++ [path]) ""
              let err = out ++ err1
              removeFile path
              return $ case exCode of
                ExitFailure n -> case n of
                  10 -> Cons
                  20 -> Inconsistent
                  _ -> Unknown $ case n of
                    30 -> "Timeout"
                    40 -> "unable to decide"
                    127 -> err
                    250 -> "Out of memory"
                    251 -> "sKizzo crashed"
                    254 -> "File not found"
                    -1 -> "sKizzo internal error"
                    -2 -> "I/O error or unexisting file"
                    -3 -> "commandline parse error"
                    -4 -> "DIMACS parse error"
                    -5 -> "sKizzo SIGBUS/SIGSEV crash"
                    -6 -> "unmanaged out of memory"
                    _ -> "Unkown, exit was: " ++ show n
                   ++ if null err then "" else ' ' : err
                _ -> Unknown "Unkown, but successful exit."

{- |
Module      :  $Header$
Description :  Helper functions for proofs in propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Helper functions for printing of Theories in DIMACS-CNF Format
-}

module Propositional.Conversions
    ( showDIMACSProblem
    , goalDIMACSProblem
    , createSignMap
    , mapClause
    ) where

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import Common.DocUtils

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Propositional.AS_BASIC_Propositional as AS
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig

import Propositional.Fold

-- | make a DIMACS Problem for SAT-Solvers
goalDIMACSProblem :: String                   -- ^ name of the theory
                  -> PState.PropProverState   -- ^ initial Prover state
                  -> AS_Anno.Named AS.FORMULA -- ^ goal to prove
                  -> [String]                 -- ^ Options (ignored)
                  -> IO String
goalDIMACSProblem thName pState conjec _ = do
    let sign = PState.initialSignature pState
        axs = PState.initialAxioms pState
    showDIMACSProblem thName sign axs $ Just conjec

-- | Translation of a Propositional Formula to a String in DIMACS Format
showDIMACSProblem :: String                     -- ^ name of the theory
                  -> Sig.Sign                   -- ^ Signature
                  -> [AS_Anno.Named AS.FORMULA] -- ^ Axioms
                  -> Maybe (AS_Anno.Named AS.FORMULA) -- ^ Conjectures
                  -> IO String                  -- ^ Output
showDIMACSProblem name fSig axs mcons = do
    let negatedCons = case mcons of
          Nothing -> []
          Just cons -> [AS_Anno.mapNamed (negForm Id.nullRange) cons]
        tAxs = map (AS_Anno.mapNamed cnf) axs
        tCon = fmap (AS_Anno.mapNamed cnf) negatedCons
        flatSens = getConj . flip mkConj Id.nullRange . map AS_Anno.sentence
        tfAxs = flatSens tAxs
        tfCon = flatSens tCon
        numVars = Set.size $ Sig.items fSig
        numClauses = length tfAxs + length tfCon
        sigMap = createSignMap fSig 1 Map.empty
        fct = map (++ " 0") . concatMap (`mapClauseAux` sigMap)
    return $ unlines $
       [ "c " ++ name, "p cnf " ++ show numVars ++ " " ++ show numClauses]
       ++ (if null tfAxs then [] else "c Axioms" : fct tfAxs)
       ++ if null tfCon || isNothing mcons then []
          else "c Conjectures" : fct tfCon

-- | Create signature map
createSignMap :: Sig.Sign
              -> Integer -- ^ Starting number of the variables
              -> Map.Map Id.Token Integer
              -> Map.Map Id.Token Integer
createSignMap sig inNum inMap =
    let it = Sig.items sig
        minL = Set.findMin it
        nSig = Sig.Sign {Sig.items = Set.deleteMin it}
    in if Set.null it then inMap else
       createSignMap nSig (inNum + 1)
                 (Map.insert (Sig.id2SimpleId minL) inNum inMap)

-- | Mapping of a single Clause
mapClause :: AS.FORMULA
          -> Map.Map Id.Token Integer
          -> String
mapClause form = unlines . map (++ " 0") . mapClauseAux form

-- | Mapping of a single Clause
mapClauseAux :: AS.FORMULA
          -> Map.Map Id.Token Integer
          -> [String]
mapClauseAux form mapL = case form of
      -- unused case: AS.Conjunction ts _ -> map (`mapLiteral` mapL) ts
      AS.True_atom _ -> []
      AS.False_atom _ -> ["-1", "1"]
      _ -> [mapLiteral form mapL]

-- | Mapping of a single literal
mapLiteral :: AS.FORMULA
           -> Map.Map Id.Token Integer
           -> String
mapLiteral f mapL = case f of
      AS.Disjunction ts _ -> intercalate " " $ map (`mapLiteral` mapL) ts
      AS.Negation n _ ->
        '-' : mapLiteral n mapL
      AS.Predication tok -> show (Map.findWithDefault 0 tok mapL)
      _ -> error $ "Impossible clause case: " ++ showDoc f ""

{- |
Module      :  $Header$
Description :  Helper functions for proofs in propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Propositional.AS_BASIC_Propositional as AS
import qualified Propositional.Prop2CNF as P2C
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
    showDIMACSProblem thName sign axs [conjec]

-- | Translation of a Propositional Formula to a String in DIMACS Format
showDIMACSProblem :: String                     -- ^ name of the theory
                  -> Sig.Sign                   -- ^ Signature
                  -> [AS_Anno.Named AS.FORMULA] -- ^ Axioms
                  -> [AS_Anno.Named AS.FORMULA] -- ^ Conjectures
                  -> IO String                  -- ^ Output
showDIMACSProblem name sig axs cons = do
    let negatedCons = if null cons then [] else
          [(AS_Anno.makeNamed "myCons"
            $ negForm Id.nullRange
            $ mkConj (map AS_Anno.sentence cons) Id.nullRange)
          { AS_Anno.isAxiom = False
          , AS_Anno.isDef = False
          , AS_Anno.wasTheorem = False } ]
    (tSig, tAxs) <- P2C.translateToCNF (sig, axs)
    (tpSig, tCon) <- P2C.translateToCNF (sig, negatedCons)
    let -- tAxs = map (AS_Anno.mapNamed cnf) axs
        -- tCon = map (AS_Anno.mapNamed cnf) negatedCons
        fSig = Sig.unite tSig tpSig
        flatSens = getConj . flip mkConj Id.nullRange . map AS_Anno.sentence
        tfAxs = flatSens tAxs
        tfCon = flatSens tCon
        numVars = Set.size $ Sig.items fSig
        numClauses = length tfAxs + length tfCon
        sigMap = createSignMap fSig 1 Map.empty
        fct sr xv = sr ++ mapClause xv sigMap
    return $ "c " ++ name ++ "\n" ++
           "p cnf " ++ show numVars ++ " " ++ show numClauses ++ "\n"
           ++ (if null tfAxs then "" else "c Axioms\n" ++ foldl fct "" tfAxs)
           ++ if null tfCon then "" else
              "c Conjectures\n" ++ foldl fct "" tfCon

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
mapClause form mapL =
    case form of
      AS.Disjunction ts _ ->
        foldl (\ sr xv -> sr ++ mapLiteral xv mapL ++ " ") "" ts
        ++ " 0 \n"
      AS.Negation (AS.Predication _) _ -> mapLiteral form mapL ++ " 0 \n"
      AS.Predication _ -> mapLiteral form mapL ++ " 0 \n"
      AS.True_atom _ -> "1 -1 0 \n"
      AS.False_atom _ -> "1 0 \n -1 0 \n"
      _ -> error "Impossible Case alternative"

-- | Mapping of a single literal
mapLiteral :: AS.FORMULA
           -> Map.Map Id.Token Integer
           -> String
mapLiteral form mapL =
    case form of
      AS.Negation (AS.Predication tok) _ ->
        '-' : show (Map.findWithDefault 0 tok mapL)
      AS.Predication tok -> show (Map.findWithDefault 0 tok mapL)
      AS.True_atom _ -> "1 -1 0 \n"
      AS.False_atom _ -> "1 0 \n-1 0 \n"
      _ -> error "Impossible Case"

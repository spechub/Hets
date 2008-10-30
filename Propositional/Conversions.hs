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
    (
     showDIMACSProblem
    ,ioDIMACSProblem
    ,goalDIMACSProblem
    ,createSignMap
    ,mapClause
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS
import qualified Common.AS_Annotation as AS_Anno
import qualified Propositional.Prop2CNF as P2C
import qualified Propositional.Sign as Sig
import qualified Common.Id as Id
import qualified Propositional.Tools as PT
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Propositional.ProverState as PState

-- | make a DIMACS Problem for SAT-Solvers
goalDIMACSProblem :: String                   -- name of the theory
                  -> PState.PropProverState   -- initial Prover state
                  -> AS_Anno.Named AS.FORMULA -- goal to prove
                  -> [String]                 -- Options (ignored)
                  -> IO String
goalDIMACSProblem thName pState conjec _ =
    let
        sign = PState.initialSignature pState
        axs  = PState.initialAxioms    pState
    in
      ioDIMACSProblem thName sign axs [conjec]

-- | IO output of DIMACS Problem
ioDIMACSProblem :: String                     -- name of the theory
                -> Sig.Sign                   -- Signature
                -> [AS_Anno.Named AS.FORMULA] -- Axioms
                -> [AS_Anno.Named AS.FORMULA] -- Conjectures
                -> IO String                  -- Output
ioDIMACSProblem name sig axs cons =
     showDIMACSProblem name sig axs cons

-- | Translation of a Propositional Formula to a String in DIMACS Format
showDIMACSProblem :: String                     -- name of the theory
                  -> Sig.Sign                   -- Signature
                  -> [AS_Anno.Named AS.FORMULA] -- Axioms
                  -> [AS_Anno.Named AS.FORMULA] -- Conjectures
                  -> IO String                  -- Output
showDIMACSProblem name sig axs cons =
    let
        nakedCons   = map (AS_Anno.sentence) cons
        negatedCons = (\ncons ->
                           case ncons of
                             [] -> []
                             _  ->
                               [(AS_Anno.makeNamed "myCons" $
                                        AS.Negation
                                              (
                                               AS.Conjunction
                                                 ncons
                                                 Id.nullRange
                                              )
                                        Id.nullRange)
                                {
                                  AS_Anno.isAxiom = False
                                , AS_Anno.isDef   = False
                                , AS_Anno.wasTheorem = False
                                }
                               ]
                      ) nakedCons
    in
              do
                (tSig, tAxs) <- P2C.translateToCNF (sig, axs)
                (tpSig, tCon) <- P2C.translateToCNF (sig, negatedCons)
                let
                    fSig         = Sig.unite tSig tpSig
                    tfAxs        = concat $ map PT.flatten $
                                   map AS_Anno.sentence tAxs
                    tfCon        = concat $ map PT.flatten $
                                   map AS_Anno.sentence tCon
                    numVars      = Set.size $ Sig.items fSig
                    numClauses   = length tfAxs + length tfCon
                    sigMap       = createSignMap fSig 1 Map.empty
                return $ "c " ++ name ++ "\n" ++
                           "p cnf " ++ show numVars ++ " " ++ show numClauses ++ "\n"++
                                        (\tflAxs ->
                                             case tflAxs of
                                               [] -> ""
                                               _  -> "c Axioms\n" ++
                                                     (foldl (\sr xv -> sr ++
                                                             mapClause xv sigMap) "" tflAxs)
                                        ) tfAxs ++
                                        (\tflCon ->
                                             case tflCon of
                                               [] -> ""
                                               _  -> "c Conjectures\n" ++
                                                     (foldl (\sr xv -> sr ++
                                                             mapClause xv sigMap) ""
                                                      tflCon)
                                        )
                           tfCon

-- | Create signature map
createSignMap :: Sig.Sign
              -> Integer                   -- | Starting number of the variables
              -> Map.Map Id.Token Integer
              -> Map.Map Id.Token Integer
createSignMap sig inNum inMap =
    let
        it   = Sig.items sig
        minL = Set.findMin it
        nSig = Sig.Sign {Sig.items = Set.deleteMin it}
    in
      case (Set.null it) of
        True  -> inMap
        False -> createSignMap
                 nSig
                 (inNum + 1)
                 (Map.insert (head $ getSimpleId minL) inNum inMap)

-- | gets simple Id
getSimpleId :: Id.Id -> [Id.Token]
getSimpleId (Id.Id toks _ _) = toks

-- | Mapping of a single Clause
mapClause :: AS.FORMULA
          -> Map.Map Id.Token Integer
          -> String
mapClause form mapL =
    case form of
      AS.Disjunction ts _ -> (foldl
                              (\sr xv -> sr ++ (mapLiteral xv mapL) ++ " ")
                              "" ts
                             )
                            ++ " 0 \n"
      AS.Negation (AS.Predication _) _ -> mapLiteral form mapL ++ " 0 \n"
      AS.Predication _    -> mapLiteral form mapL ++ " 0 \n"
      AS.True_atom   _     -> "1 -1 0 \n"
      AS.False_atom  _     -> "1 0 \n -1 0 \n"
      _                   -> error "Impossible Case alternative"

-- | Mapping of a single literal
mapLiteral :: AS.FORMULA
           -> Map.Map Id.Token Integer
           -> String
mapLiteral form mapL =
    case form of
      AS.Negation (AS.Predication tok) _ -> "-" ++
              show (Map.findWithDefault 0 tok mapL)
      AS.Predication tok   -> show (Map.findWithDefault 0 tok mapL)
      AS.True_atom   _     -> "1 -1 0 \n"
      AS.False_atom  _     -> "1 0 \n-1 0 \n"
      _                    -> error "Impossible Case"

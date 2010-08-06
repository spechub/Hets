{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Jonatzhan von Schroeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Data structures and initialising functions for Prover state and configurations.

-}

module QBF.ProverState where

import Logic.Prover as LP

import Propositional.Sign
import qualified QBF.Morphism as QMorphism
import qualified QBF.AS_BASIC_QBF as AS
import QBF.Tools

import Data.List (intercalate, elemIndex)
import qualified Control.Arrow

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.Id

-- * Data structures

data QBFProverState = QBFProverState
    { initialAxioms :: [AS_Anno.Named AS.FORMULA]
    , initialSignature :: Sign
    , freeDefs :: [LP.FreeDefMorphism AS.FORMULA QMorphism.Morphism]
    } deriving (Show)

{- |
  Creates an initial qbf prover state
-}
qbfProverState :: Sign -- ^ QBF signature
                 -> [AS_Anno.Named AS.FORMULA] -- ^ list of named QBF formulas
                 -> [LP.FreeDefMorphism AS.FORMULA QMorphism.Morphism]
                 -- ^ freeness constraints
                 -> QBFProverState
qbfProverState sign aSens freedefs =
    let
        axioms = prepareSenNames transSenName $ filter AS_Anno.isAxiom aSens
    in
        foldl insertSentence
        QBFProverState
        {
          initialAxioms = []
        , initialSignature = sign
        , freeDefs = freedefs
        } axioms

transSenName :: String -> String
transSenName = id

{- |
  Inserts a named SoftFOL term into SoftFOL prover state.
-}
insertSentence :: QBFProverState -- ^ prover state containing the axioms
                  -> AS_Anno.Named AS.FORMULA -- ^ formula to add
                  -> QBFProverState
insertSentence pst f = pst { initialAxioms = initialAxioms pst ++ [f] }

{- |
  Pretty printing QBF goal in QDIMACS format.
-}
showQDIMACSProblem :: String -- ^ theory name
                -> QBFProverState -- ^ prover state
                -> AS_Anno.Named AS.FORMULA -- ^ goal
                -> [String] -- ^ extra options
                -> IO String -- ^ formatted output of the goal
showQDIMACSProblem thName pst nGoal _ =
    let
        fList :: AS.FORMULA -> [[AS.FORMULA]]
        fList (AS.Conjunction fs _) = map (\ f ->
          case f of
             (AS.Disjunction xs _) -> xs
             a@(AS.TrueAtom _) -> [a]
             a@(AS.FalseAtom _) -> [a]
             p@(AS.Predication _) -> [p]
             x -> error ("Unexpected " ++ show x)
           ) fs
        fList (AS.Disjunction xs _) = [xs]
        fList a@(AS.TrueAtom _) = [[a]]
        fList a@(AS.FalseAtom _) = [[a]]
        fList p@(AS.Predication _) = [[p]]
        fList n@(AS.Negation _ _) = [[n]]
        fList f = error ("Unexpected " ++ show f)
        atomToNum :: AS.FORMULA -> Int
        atomToNum f = case f of
                           AS.TrueAtom _ -> trueAtom
                           AS.FalseAtom _ -> falseAtom
                           AS.Negation x _ -> -(atomToNum x)
                           AS.Predication t ->
                             case (elemIndex t qf, elemIndex t qe) of
                                  (Just i, Nothing) -> 1 + i
                                  (Nothing, Just i) -> lqf + 1 + i
                                  _ -> error ("Unknown variable " ++ show f)
                           t -> error ("Unexpected " ++ show t)

        axioms = map (AS_Anno.senAttr Control.Arrow.&&& AS_Anno.sentence)
                     (initialAxioms pst)
        goal = AS_Anno.sentence nGoal
        {- first we need to make sure that we simply can move out all
        quantifiers by making sure that every quantified variable is unique -}
        maxVarLen = maximum (map (length . tokStr)
                              (concatMap getVars (goal : (snd . unzip) axioms)))
        prefix = replicate maxVarLen '_'
        (c, goal1) = uniqueQuantifiedVars 1 prefix goal
        axioms1 = snd (foldr (\ (s, f) (c', a') -> let
            (c1, f') = uniqueQuantifiedVars c' prefix f
          in
            (c1, (s, f') : a')) (c, []) axioms)
        -- next we transform everything into cnf form
        axioms2 = map (Control.Arrow.second (fList . cnf . removeQuantifiers))
                    axioms1
        goal2 = (fList . cnf . removeQuantifiers) goal1
        {- find out how the variables are quantified - variables that
        are not explictly quantified are treated to be existentially
        quantified since a theory holds iff it has a model -}
        qv = foldr joinQuantifiedVars quantifiedVars
          (getQuantifiedVars goal1 : map (getQuantifiedVars . snd) axioms1)
        qf = universallyQ qv
        qe = existentiallyQ qv ++ notQ qv
        lqf = length qf
        lqe = length qe
        (cTrueAtom, cFalseAtom) = foldl
          (\ (r1, r2) (r3, r4) -> (r1 || r3, r2 || r4))
          (False, False) ((containsAtoms . AS_Anno.sentence) nGoal :
            map (containsAtoms . AS_Anno.sentence) (initialAxioms pst))
        goalN = AS_Anno.senAttr nGoal
        trueAtom = lqf + lqe + (if cTrueAtom then 1 else 0)
        falseAtom = -(trueAtom + (if cFalseAtom then 1 else 0))
        base = 3 + (if lqf > 0 then 1 else 0)
          + (if lqe > 0 then 1 else 0) + length axioms2
        axiomsL = sum (map (length . snd) axioms2)
    in
        return (unlines ([
          "c Problem" ++ thName,
          "c The goal " ++ goalN ++ " is on the lines "
          ++ show (base + axiomsL + 1) ++ "-"
          ++ show (base + axiomsL + length goal2)
          ] ++ snd (foldl
                      (\ (cnt, lst) (name, fs) ->
                        ( cnt + length fs,
                          lst ++
                          ["c The axiom " ++ name ++ " is on the lines "
                            ++ show (base + cnt)
                            ++ "-"
                            ++ show (base + cnt + length fs - 1)
                          ]
                        )
                      ) (1, []) axioms2)
          ++ ["p cnf "
               ++ show (-falseAtom)
               ++ " "
               ++ show (length goal2 + axiomsL)
             ]
          ++ (if qf == [] then []
              else ["a " ++ intercalate " " (map show ([1 .. lqf] ++ [0]))])
          ++ (if qe == [] then []
              else ["e " ++ intercalate " " (map show
                     ([(lqf + 1) .. (lqf + lqe)] ++ [0]))])
          ++ foldl (++) [] (map
                 (\ (_, f) -> map
                                (\ fs -> intercalate " "
                                          (map (show . atomToNum) fs ++ ["0"])
                                ) f
                 ) (axioms2 ++ [("", goal2)]))
          ++ (if cTrueAtom then [show trueAtom, " 0"] else [])
          ++ (if cFalseAtom then [show falseAtom, " 0"] else [])))

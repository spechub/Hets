{- |
Module      :  $Header$
Description :  Provers for propositional logic
Copyright   :  (c) Till Mossakowski, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

A truth table prover for propositional logic.
Inefficient, but useful for learning purposes.
-}

module Propositional.ProveWithTruthTable
    (
     ttProver,
     ttConsistencyChecker,
     ttConservativityChecker,
     allModels
    )
    where

-- import Debug.Trace

import Text.Tabular
import Text.Tabular.AsciiArt

import Propositional.AS_BASIC_Propositional
import Propositional.Sign
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig
import Propositional.Sublogic(PropSL,top)

import qualified Logic.Prover as LP

import qualified Interfaces.GenericATPState as ATPState
import GUI.GenericATP
import GUI.Utils (infoDialog, createTextSaveDisplay)

import Common.ProofTree
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Common.OrderedMap as OMap
import System.IO
import System.IO.Unsafe

import Common.Consistency
import qualified Common.Result as Result



-- * Prover implementation

-- | the name of the prover
ttS :: String
ttS = "truth tables"

-- maximal size of the signature
maxSigSize :: Int
maxSigSize = 17

-- display error message when signature is too large
sigTooLarge :: Int -> IO()
sigTooLarge sigSize =
   infoDialog "Signature is too large"
              ("Signature is too large. "++
               "It should contain < "++show maxSigSize++" symbols, "++
               "but it contains "++show sigSize++" symbols.")

ttHelpText :: String
ttHelpText = "An implementation of the truth table method.\n"++
                 "Very inefficient, but useful for learning and teaching\n"++
                 "Works well for signatures with less than "++show maxSigSize++
                 " symbols."

{- |
  Models and evaluation of sentences
-}

type Model = Set.Set Id.Id -- a model specifies which propositions are true

-- | show Bools in truth table
showBool :: Bool -> String
showBool True = "T"
showBool False = "F"

-- | evaluation of sentences in a model
eval :: Model -> FORMULA -> Bool
eval m (Negation phi _) = not (eval m phi)
eval m (Conjunction phis _) = and (map (eval m) phis)
eval m (Disjunction phis _) = or (map (eval m) phis)
eval m (Implication phi1 phi2 _) =
       not (eval m phi1) || (eval m phi2)
eval m (Equivalence phi1 phi2 _) =
       (eval m phi1) == (eval m phi2)
eval _ (True_atom _) = True
eval _ (False_atom _) = False
eval m (Predication ident) = Id.simpleIdToId ident `Set.member` m

evalNamed :: Model -> AS_Anno.Named FORMULA -> Bool
evalNamed m phi = eval m (AS_Anno.sentence phi)


{- |
  Evaluation of (co)freeness constraints
-}


-- | amalgamation of models
amalg :: Model -> Model -> Model
amalg = Set.union

data FormulaOrFree =
     Formula FORMULA
   | FreeConstraint (LP.FreeDefMorphism FORMULA PMorphism.Morphism)


evalNamedFormulaOrFree :: Model -> AS_Anno.Named FormulaOrFree -> Bool
evalNamedFormulaOrFree m phi = evalFormulaOrFree m (AS_Anno.sentence phi)

evalFormulaOrFree :: Model -> FormulaOrFree -> Bool
evalFormulaOrFree m (Formula phi) = eval m phi
evalFormulaOrFree m (FreeConstraint freedef) = evalFree m freedef

reduceModel :: Sig.Sign -> Model -> Model
reduceModel sig m = Set.intersection m (items sig)

leq :: Model -> Model -> Bool
leq = Set.isSubsetOf

isMin :: Bool -> Model -> [Model] -> Bool
isMin isCo m models =
   all (\m' -> if isCo then leq m' m else leq m m') models

evalFree :: Model
              -> LP.FreeDefMorphism FORMULA PMorphism.Morphism
              -> Bool
evalFree m freedef =
  let diffsig = Sign ((items freetar) `Set.difference` (items freesrc))
      mred = reduceModel freesrc m
      modelsOverMred = map (mred `amalg`) (allModels diffsig)
      modelClass = foldr (filter . (flip eval)) modelsOverMred freeth
  in all (eval m) freeth        -- the model satisfies the axioms ...
     && isMin isCo m modelClass -- ... and is the minimal one that does so
  where freemor = LP.freeDefMorphism freedef
        freesrc = PMorphism.source freemor
        freetar = PMorphism.target freemor
        freeth = map AS_Anno.sentence $ LP.freeTheory freedef
        isCo = LP.isCofree freedef



-- | generate all models for a signature
allModels :: Sign -> [Model]
allModels sig = allModels1 $ Set.toList $ items sig
  where allModels1 [] = [Set.empty]
        allModels1 (p:rest) =
          let models = allModels1 rest
           in models ++ map (Set.insert p) models

data TTExtRow =
     TTExtRow { rextprops, rextaxioms :: [Bool],
                rextIsModel :: Bool
              }

data TTRow =
     TTRow { rprops, raxioms :: [Bool],
             rgoal :: Maybe Bool,
             rextrows :: [TTExtRow],
             rIsModel :: Bool,
             rIsOK :: Bool
           }

data TTHead =
     TTHead { hprops, haxioms, hextprops, hextaxioms :: [String],
              hgoal :: Maybe String
            }

data TruthTable =
     TruthTable { thead :: TTHead,
                  trows :: [TTRow] }

renderTT :: TruthTable -> Table String
renderTT tt = Table rowHeaders header table
  where
  hextpropsTT = hextprops (thead tt)
  hextaxiomsTT = hextaxioms (thead tt)
  rowsTT = trows tt
  header = Group DoubleLine
           ( [ Group SingleLine (map Header (hprops (thead tt)))
             , Group SingleLine (map Header (haxioms (thead tt)))]
             ++ (if null hextpropsTT && null hextaxiomsTT then []
                 else [ Header ""
                      , Group SingleLine (map Header hextpropsTT)
                      , Group SingleLine (map Header hextaxiomsTT)])
             ++ case hgoal (thead tt) of
                 Nothing -> []
                 Just g -> [Group DoubleLine [Header g]])
  rowtype r = (if rIsModel r then "M" else " ")
              ++(if rIsOK r then (if rIsModel r then "+" else "o")
                            else "-")
  rowHeader r =
     Group NoLine (Header (rowtype r) :
                   map (const (Header "")) [2..length (rextrows r)])
  rowHeaders =
    if all (null . rextrows) rowsTT
    then Group NoLine (map (Header . rowtype) rowsTT)
    else Group SingleLine (map rowHeader rowsTT)
  makeExtRow e =
    (if rextIsModel e then "M" else "") :
    map showBool (rextprops e) ++
    map showBool (rextaxioms e)
  makeRow r =
    let common = map showBool (rprops r) ++
                 map showBool (raxioms r) ++
                 case (rgoal r) of
                   Nothing -> []
                   Just g -> [showBool g]
        emptyPrefix = map (const "") [1..length common]
    in case map makeExtRow (rextrows r) of
       [] -> [common]
       (e:extrows) -> (common++e):map (emptyPrefix ++) extrows
  table = concatMap makeRow rowsTT


{- |
  The Prover implementation.

  Implemented are: a prover GUI.
-}
ttProver :: LP.Prover Sig.Sign FORMULA PMorphism.Morphism PropSL ProofTree
ttProver = (LP.mkProverTemplate ttS top ttProveGUI)
    { LP.proveCMDLautomatic = Nothing
    , LP.proveCMDLautomaticBatch = Nothing}

{- |
   The Consistency Cheker.
-}
ttConsistencyChecker :: LP.ConsChecker Sig.Sign FORMULA PropSL
                                  PMorphism.Morphism ProofTree
ttConsistencyChecker = LP.mkProverTemplate ttS top consCheck

consCheck :: String -> LP.TheoryMorphism Sig.Sign FORMULA
             PMorphism.Morphism ProofTree
          -> [LP.FreeDefMorphism FORMULA PMorphism.Morphism] -- ^ free definitions
          -> IO([LP.Proof_status ProofTree])
consCheck thName tm _freedefs =
  case LP.t_target tm of
    LP.Theory sig nSens ->
      let sigSize = Set.size (items sig) in
      if sigSize >= maxSigSize then do
        sigTooLarge sigSize
        return []
      else do
        let axs = filter (AS_Anno.isAxiom . snd) $ OMap.toList nSens
            models = allModels sig
            sigList = Set.toList $ items sig
            heading =
              TTHead { hprops = map show sigList,
                       haxioms = map fst axs,
                       hextprops = [], hextaxioms = [],
                       hgoal = Nothing
                     }
            mkRow m =
              let evalAx = map (eval m . AS_Anno.sentence . snd) axs
                  isModel = and evalAx
              in TTRow { rprops = map (`Set.member` m) sigList,
                         raxioms = evalAx,
                         rextrows = [],
                         rgoal = Nothing,
                         rIsModel = isModel,
                         rIsOK = isModel
                       }
            rows = map mkRow models
            isOK = or (map rIsOK rows)
            table = TruthTable { thead = heading,
                                 trows = rows
                               }
            title = if isOK then "Theory is consistent"
                            else "Theory is inconsistent"
            legend = "Legend:\nM+ = model of the axioms\n"++
                     " - = not a model of the axioms\n"
            body = legend++"\n"++render id (renderTT table)
        createTextSaveDisplay title (thName++".tt") body
        return []


-- ** prover GUI

{- |
  Invokes the generic prover GUI.
-}
ttProveGUI :: String -- ^ theory name
          -> LP.Theory Sig.Sign FORMULA ProofTree
          -> [LP.FreeDefMorphism FORMULA PMorphism.Morphism] -- ^ free definitions
          -> IO([LP.Proof_status ProofTree]) -- ^ proof status for each goal
ttProveGUI thName th freedefs =
--  trace (show freedefs) $
    genericATPgui (atpFun thName) True (LP.prover_name ttProver) thName th
                  freedefs emptyProofTree

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
       -> ATPState.ATPFunctions Sig.Sign FORMULA PMorphism.Morphism ProofTree PState.PropProverState
atpFun thName = ATPState.ATPFunctions
                {
                  ATPState.initialProverState = PState.propProverState
                , ATPState.goalOutput         = goalProblem thName
                , ATPState.atpTransSenName    = PState.transSenName
                , ATPState.atpInsertSentence  = PState.insertSentence
                , ATPState.proverHelpText     = ttHelpText
                , ATPState.runProver          = runTt
                , ATPState.batchTimeEnv       = ""
                , ATPState.fileExtensions     = ATPState.FileExtensions{ATPState.problemOutput = ".tt",
                                                                        ATPState.proverOutput = ".tt",
                                                                        ATPState.theoryConfiguration = ".tt"}
                , ATPState.createProverOptions = createTtOptions
                }

defaultProof_status :: AS_Anno.Named FORMULA -> LP.Proof_status ProofTree
defaultProof_status nGoal =
  (LP.openProof_status (AS_Anno.senAttr nGoal)
                       (LP.prover_name ttProver)
                       emptyProofTree)


{- |
  Runs tt.
-}

runTt :: PState.PropProverState
           -- logical part containing the input Sign and
           -- axioms and possibly goals that have been proved
           -- earlier as additional axioms
           -> ATPState.GenericConfig ProofTree
           -- configuration to use
           -> Bool
           -- True means save DIMACS file
           -> String
           -- Name of the theory
           -> AS_Anno.Named FORMULA
           -- Goal to prove
           -> IO (ATPState.ATPRetval
                 , ATPState.GenericConfig ProofTree
                 )
           -- (retval, configuration with proof status and complete output)
runTt pState cfg _ _thName nGoal =
  let sig = PState.initialSignature pState
      sigSize = Set.size $ items sig
   in if sigSize >= maxSigSize then do
        sigTooLarge sigSize
        return (ATPState.ATPTLimitExceeded,
                cfg{ATPState.proof_status = defaultProof_status nGoal})
      else do
       let axs = PState.initialAxioms pState
           freedefs = PState.freeDefs pState
           nameFree fd =
              AS_Anno.makeNamed (if LP.isCofree fd then "cofree" else "free")
                                (FreeConstraint fd)
           sens = map (AS_Anno.mapNamed Formula) axs ++ map nameFree freedefs
           models = allModels sig
           sigList = Set.toList $ items sig
           heading =
             TTHead { hprops = map show sigList,
                      haxioms = map AS_Anno.senAttr sens,
                      hextprops = [], hextaxioms = [],
                      hgoal = Just $ AS_Anno.senAttr nGoal
                    }
           mkRow m =
             let evalAx = map (evalNamedFormulaOrFree m) sens
                 evalGoal = evalNamed m nGoal
                 isModel = and evalAx
             in TTRow { rprops = map (`Set.member` m) sigList,
                        raxioms = evalAx,
                        rextrows = [],
                        rgoal = Just evalGoal,
                        rIsModel = isModel,
                        rIsOK = not isModel || evalGoal
                      }
           rows = map mkRow models
           isOK = and (map rIsOK rows)
           consistent = or (map rIsModel rows)
           table = TruthTable { thead = heading,
                                trows = rows
                              }
           legend = "Legend:\nM = model of the premises\n"++
                    "+ = OK, model fulfills conclusion\n"++
                    "- = not OK, counterexample for logical consequence\n"++
                    "o = OK, premises are not fulfilled, hence conclusion is irrelevant\n"
           body = legend++"\n"++render id (renderTT table)
       let status = (defaultProof_status nGoal)
                     { LP.goalStatus = if isOK then LP.Proved $ Just consistent
                                               else LP.Disproved,
                       LP.usedAxioms = map AS_Anno.senAttr sens
                     }
       return (ATPState.ATPSuccess,
               cfg{ATPState.proof_status = status,
                   ATPState.resultOutput = [body]})

{- |
  Creates a list of all options the truth table prover runs with.
  Only Option is the timelimit
-}
createTtOptions :: ATPState.GenericConfig ProofTree -> [String]
createTtOptions _cfg = []
   -- [(show $ configTimeLimit cfg)]

goalProblem :: String                   -- name of the theory
                  -> PState.PropProverState   -- initial Prover state
                  -> AS_Anno.Named FORMULA -- goal to prove
                  -> [String]                 -- Options (ignored)
                  -> IO String
goalProblem _ _ _ _ =
  return ""

{- |
  Conservativity check
-}

-- | Conservativity Check via truth table

-- TODO: check for injectivity!

ttConservativityChecker ::
              (Sign, [AS_Anno.Named FORMULA]) -- ^ Initial sign and formulas
           -> PMorphism.Morphism              -- ^ morhpism between specs
           -> [AS_Anno.Named FORMULA]         -- ^ Formulas of extended spec
           -> Result.Result (Maybe (ConsistencyStatus, [FORMULA]))
ttConservativityChecker (_, srcSens) mor tarSens=
  let srcAxs        = filter AS_Anno.isAxiom srcSens
      tarAxs        = filter AS_Anno.isAxiom tarSens
      srcSig        = items $ PMorphism.source mor
      imageSig      = Set.map (PMorphism.applyMorphism mor) $ srcSig
      imageSigList  =  Set.toList imageSig
      tarSig        = items $ PMorphism.target mor
      newSig        = Set.difference tarSig imageSig
      sigSize       = Set.size tarSig
  in
    if sigSize >= maxSigSize then do
       return (seq (unsafePerformIO $ sigTooLarge sigSize) Nothing)
    else do
      let imageAxs = map (AS_Anno.mapNamed (PMorphism.mapSentenceH mor)) srcAxs
          models = allModels (Sign imageSig)
          newSigList = Set.toList newSig
          heading =
            TTHead { hprops = map show imageSigList,
                     haxioms = map AS_Anno.senAttr srcAxs,
                     hextprops =  map show newSigList,
                     hextaxioms = map AS_Anno.senAttr tarAxs,
                     hgoal = Nothing
                   }
          mkRow m =
            let evalAx = map (evalNamed m) imageAxs
                isModel = and evalAx
                extmodels = allModels (Sign newSig)
                extrow m' =
                  let evalExtAx = map (evalNamed (m `amalg` m')) tarAxs
                      isExtModel = and evalExtAx
                   in TTExtRow { rextprops = map (`Set.member` m') newSigList,
                                rextaxioms = evalExtAx,
                                rextIsModel = isExtModel
                              }
                extrows = map extrow extmodels
            in TTRow { rprops = map (`Set.member` m) imageSigList,
                       raxioms = evalAx,
                       rgoal = Nothing,
                       rextrows = if isModel then extrows else [],
                       rIsModel = isModel,
                       rIsOK = not isModel || or (map rextIsModel extrows)
                     }
          rows = map mkRow models
          isOK = and (map rIsOK rows)
          table = TruthTable { thead = heading,
                               trows = rows
                             }
          title = "The extension is "++
                  (if isOK then "" else "not ")++
                  "conservative"
          legend = "Legend:\n"++
                   "M = model of the axioms\n"++
                   "+ = OK, has expansion\n"++
                   "- = not OK, has no expansion, "++
                       "hence conservativity fails\n"++
                   "o = OK, not a model of the axioms, "++
                       "hence no expansion needed\n"
          body = legend++"\n"++render id (renderTT table)
          disp = createTextSaveDisplay title "unnamed" body
          res = if isOK then Conservative else Inconsistent
      return (seq (unsafePerformIO $ disp) (Just (res,[])))


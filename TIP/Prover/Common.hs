module TIP.Prover.Common where

import TIP.AbsTIP
import TIP.Utils
import Common.ProofTree
import Common.Utils
import Interfaces.GenericATPState
import Data.Maybe (fromMaybe,maybeToList)
import qualified Data.IntMap.Strict as IM
import Control.Monad (when)
import Control.Arrow ((***),second)

data TIPQuirks = TIPQuirk
  { noAnnotations :: Bool
  , noPluralDatatype :: Bool
  }
noTIPQuirks :: TIPQuirks
noTIPQuirks = TIPQuirk False False

mkTheoryFileName :: String -> Decl -> String
mkTheoryFileName theoryName goal =
  basename (theoryName ++ '_' : fromMaybe "" (getFormulaName goal) ++ ".smt2")

makeGoal :: Decl -> Decl
makeGoal (Formula _ gAttrs gExpr) = Formula Prove gAttrs gExpr
makeGoal (FormulaPar _ gAttrs gPar gExpr) = FormulaPar Prove gAttrs gPar gExpr
makeGoal d = d

generateProblem :: TIPQuirks -> Start -> Maybe Decl -> (Start, IM.IntMap Int)
generateProblem quirks (Start decls) mGoal =
  (Start generatedDecls, blame) where
    goalAdded = decls ++ map makeGoal (maybeToList mGoal)
    applyAnno = if noAnnotations quirks then stripAttrs else id
    annoApplied = map applyAnno goalAdded
    applyPlural = if noPluralDatatype quirks then singularizeDatas else (:[])
    pluralAppliedBlame =
      concatMap ((uncurry zip).(applyPlural *** repeat)) (zip annoApplied [1..])
    generatedDecls = map fst pluralAppliedBlame
    blame = foldr ((uncurry IM.insert).(second snd)) IM.empty $ zip [1..] pluralAppliedBlame

prepareProverInput :: Start
                   -> GenericConfig ProofTree
                   -> Bool
                   -> String
                   -> Decl
                   -> TIPQuirks
                   -> String
                   -> IO (String, IM.IntMap Int)
prepareProverInput spec _cfg saveFile theoryName goal quirks _prover_name = 
  do
    let (tipProblem, blame) = generateProblem quirks spec $ Just goal
    let theoryFileName = mkTheoryFileName theoryName goal
    let tipProblemString = printTIP tipProblem
    problemFileName <- getTempFile tipProblemString theoryFileName
    saveProblemFileIfNeeded theoryFileName tipProblemString
    return (problemFileName,blame)
  where
    saveProblemFileIfNeeded :: String -> String -> IO ()
    saveProblemFileIfNeeded theoryFileName tipProblemString =
      when saveFile $ writeFile theoryFileName tipProblemString

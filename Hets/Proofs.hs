module Hets.Proofs (
    automatic,
    automaticFromList,
    freeness,
    normalForm,
    globalSubsume,
    globalDecomposition,
    localInference,
    localDecomposition
) where

import Proofs.Freeness (freeness)
import Proofs.NormalForm (normalForm,normalFormRule, normalFormLibEnv)
import Proofs.Automatic (automatic, automaticFromList)
import Proofs.Global (globSubsume, globDecomp)
import Proofs.Local (localInference, locDecomp)
import Proofs.Composition (composition, compositionCreatingEdges)

globalSubsume = globSubsume
globalDecomposition = globDecomp

localDecomposition = locDecomp
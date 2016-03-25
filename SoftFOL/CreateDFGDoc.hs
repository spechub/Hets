{- |
Module      :  ./SoftFOL/CreateDFGDoc.hs
Description :  Generating DFG Doc out of SPASS theories.
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-protable(Logic)

Printing a (G_theory CASL _) into a DFG Doc.

-}

module SoftFOL.CreateDFGDoc (printTheoryAsSoftFOL) where

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Static.GTheory

import Common.AS_Annotation as AS_Anno
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.IRI (IRI)
import Common.ProofUtils
import Common.Result

import CASL.Logic_CASL
import CASL.Sublogic

import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.SuleCFOL2SoftFOL

import SoftFOL.Logic_SoftFOL
import SoftFOL.Conversions
import SoftFOL.Translate
import SoftFOL.Sign

import SoftFOL.PrintTPTP

spassConsTimeLimit :: Int
spassConsTimeLimit = 500

printTheoryAsSoftFOL :: IRI
         -> Int -- ^ 0 = DFG, 1 = TPTP
         -> Bool
            {- ^ if True a conjecture false is added otherwise
                 its a theory without its own conjectures. -}
         -> G_theory -> IO (Maybe Doc)
printTheoryAsSoftFOL sn lang checkConsistency
  gth@(G_theory lid _ (ExtSign sign _) _ thSens _) =
    maybe (return Nothing)
          (\ (sign1, sens1) ->
               do prob <- genSoftFOLProblem
                              thName
                              (spLogicalPart sign1 sens1)
                              (if checkConsistency
                               then Just falseConj
                               else Nothing)
                  return $ Just $ printOut
                         prob {settings = [SPSettings
                                            {settingName = SPASS,
                                             settingBody = flags}]})
                         -- (prob {settings = flags}))

      (resultToMaybe (if lessSublogicComor (sublogicOfTh gth) $
          Comorphism suleCFOL2SoftFOL
       then coerceBasicTheory lid CASL "" (sign, sens)
              >>= wrapMapTheory suleCFOL2SoftFOL
       else (if lessSublogicComor (sublogicOfTh gth) $ Comorphism idCASL
        then coerceBasicTheory lid CASL "" (sign, sens)
              >>= wrapMapTheory idCASL
              >>= wrapMapTheory defaultCASL2SubCFOL
              >>= wrapMapTheory suleCFOL2SoftFOL
        else if lessSublogicComor (sublogicOfTh gth) $
                Comorphism idCASL_nosub
             then coerceBasicTheory lid CASL "" (sign, sens)
                      >>= wrapMapTheory idCASL_nosub
                      >>= wrapMapTheory CASL2PCFOL
                      >>= wrapMapTheory defaultCASL2SubCFOL
                      >>= wrapMapTheory suleCFOL2SoftFOL
             else coerceBasicTheory lid SoftFOL "" (sign, sens))))
  where
        printOut = case lang of
                     0 -> pretty
                     1 -> printTPTP
                     _ -> pretty
        sens = toNamedList thSens
        thName = show sn

        spLogicalPart sig sen =
                            foldl insertSentence
                                  (signToSPLogicalPart sig)
                                  (reverse $
                                   prepareSenNames transSenName sen)

        flags = if checkConsistency
                then [SPFlag "set_flag" ["TimeLimit", show spassConsTimeLimit]
                     , SPFlag "set_flag" ["DocProof", "1"]]
                else []

        falseConj = (makeNamed "inconsistent" falseSen)
                    { isAxiom = False }
        falseSen = simpTerm SPFalse

        max_nosub_SPASS = caslTop { cons_features = emptyMapConsFeature }
        max_sub_SPASS = caslTop { sub_features = LocFilSub }
        idCASL = mkIdComorphism CASL max_sub_SPASS
        idCASL_nosub = mkIdComorphism CASL max_nosub_SPASS

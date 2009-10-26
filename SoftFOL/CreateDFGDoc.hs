{- |
Module      :  $Header$
Description :  Generating DFG Doc out of SPASS theories.
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
import Common.Id
import Common.LibName
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

printTheoryAsSoftFOL :: LibName -> SIMPLE_ID
         -> Int -- ^ 0 = DFG, 1 = TPTP
         -> Bool
            -- ^ if True a conjecture false is added otherwise
            -- its a theory without its own conjectures.
         -> G_theory -> IO (Maybe Doc)
printTheoryAsSoftFOL ln sn lang checkConsistency
  gth@(G_theory lid (ExtSign sign _) _ thSens _) =
    maybe (return Nothing)
          (\ (sign1,sens1) ->
               do prob <- genSoftFOLProblem
                              thName
                              (spLogicalPart sign1 sens1)
                              (if checkConsistency
                               then Just falseConj
                               else Nothing)
                  return $ Just $ printOut $
                         (prob {settings = [SPSettings
                                            {settingName = SPASS,
                                             settingBody = flags}]}))
                         -- (prob {settings = flags}))

      (if lessSublogicComor (sublogicOfTh gth) $
          Comorphism SuleCFOL2SoftFOL
       then resultToMaybe
             (coerceBasicTheory lid CASL "" (sign,sens)
              >>= wrapMapTheory SuleCFOL2SoftFOL)
       else
        if lessSublogicComor (sublogicOfTh gth) $ Comorphism idCASL
        then resultToMaybe
             (coerceBasicTheory lid CASL "" (sign,sens)
              >>= wrapMapTheory idCASL
              >>= wrapMapTheory defaultCASL2SubCFOL
              >>= wrapMapTheory SuleCFOL2SoftFOL)
        else if lessSublogicComor (sublogicOfTh gth) $
                Comorphism idCASL_nosub
             then resultToMaybe
                     (coerceBasicTheory lid CASL "" (sign,sens)
                      >>= wrapMapTheory idCASL_nosub
                      >>= wrapMapTheory CASL2PCFOL
                      >>= wrapMapTheory defaultCASL2SubCFOL
                      >>= wrapMapTheory SuleCFOL2SoftFOL)
             else resultToMaybe $
                 coerceBasicTheory lid SoftFOL "" (sign,sens))
  where
        printOut = case lang of
                     0 -> pretty
                     1 -> printTPTP
                     _ -> pretty
        sens = toNamedList thSens
        thName = shows (getLibId ln) "_" ++ show sn

        spLogicalPart sig sen =
                            foldl insertSentence
                                  (signToSPLogicalPart sig)
                                  (reverse $
                                   prepareSenNames transSenName sen)

        flags = if checkConsistency
                then [SPFlag "set_flag" ["TimeLimit",(show spassConsTimeLimit)]
                     ,SPFlag "set_flag" ["DocProof", "1"]]
                else []

        falseConj = (makeNamed "inconsistent" falseSen)
                    {
                      isAxiom    = False
                    , isDef      = False
                    , wasTheorem = False
                    }
        falseSen = simpTerm SPFalse

        max_nosub_SPASS = caslTop { cons_features = emptyMapConsFeature }
        max_sub_SPASS = caslTop { sub_features = LocFilSub }
        idCASL = mkIdComorphism CASL max_sub_SPASS
        idCASL_nosub = mkIdComorphism CASL max_nosub_SPASS

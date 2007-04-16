{- |
Module      :  $Header$
Description :  Generating DFG Doc out of SPASS theories.
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-protable(Logic)

Printing a (G_theory CASL _) into a DFG Doc.

-}

module SPASS.CreateDFGDoc (printTheoryAsDFG) where

import Data.Maybe

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Static.DevGraph

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result
import Common.AS_Annotation as AS_Anno
import Common.ProofUtils

import Syntax.AS_Library
import Syntax.Print_AS_Library ()

import CASL.Logic_CASL
import CASL.Sublogic

import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SPASS

import SPASS.Logic_SPASS
import SPASS.Conversions
import SPASS.Translate
import SPASS.Sign


spassConsTimeLimit :: Int
spassConsTimeLimit = 500

printTheoryAsDFG :: LIB_NAME -> SIMPLE_ID 
         -> Bool 
            -- ^ if True a conjecture false is added otherwise 
            -- its a theory without a conjecture.
         -> G_theory -> IO (Maybe Doc)
printTheoryAsDFG ln sn checkConsistency gth@(G_theory lid sign _ thSens _) = 
    maybe (return Nothing)
          (\ (sign1,sens1) ->
               do prob <- genSPASSProblem 
                              thName
                              (spLogicalPart sign1 sens1)
                              (if checkConsistency
                               then Just falseConj
                               else Nothing)
                  return $ Just $ pretty $ 
                         (prob {settings = flags}))
 
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
              >>= wrapMapTheory CASL2SubCFOL
              >>= wrapMapTheory SuleCFOL2SoftFOL)
        else if lessSublogicComor (sublogicOfTh gth) $ 
                Comorphism idCASL_nosub
             then resultToMaybe  
                     (coerceBasicTheory lid CASL "" (sign,sens)
                      >>= wrapMapTheory idCASL_nosub
                      >>= wrapMapTheory CASL2PCFOL
                      >>= wrapMapTheory CASL2SubCFOL
                      >>= wrapMapTheory SuleCFOL2SoftFOL)
             else resultToMaybe $
                 coerceBasicTheory lid SoftFOL "" (sign,sens))


  where sens = toNamedList thSens
        thName = shows (getLIB_ID ln) "_" ++ show sn

        spLogicalPart sig sen = 
                            foldl insertSentence 
                                  (signToSPLogicalPart sig) 
                                  (reverse $ 
                                   prepareSenNames transSenName sen)

        flags = if checkConsistency
                then [SPFlag "TimeLimit" (show spassConsTimeLimit)
                     ,SPFlag "DocProof" "1"]
                else []

        falseConj = (makeNamed "inconsistent" falseSen)
                    {
                      isAxiom    = False
                    , isDef      = False
                    , wasTheorem = False
                    }
        falseSen = SPSimpleTerm SPFalse

        caslTop :: CASL_Sublogics -- fix the instance!
        caslTop = top
        max_nosub_SPASS = 
               caslTop {cons_features =
                        (cons_features caslTop) {emptyMapping = True} }
        max_sub_SPASS = caslTop { sub_features = LocFilSub
                               , cons_features = 
                                   (cons_features caslTop) 
                                   {onlyInjConstrs=False}}
        idCASL = IdComorphism CASL max_sub_SPASS
        idCASL_nosub = IdComorphism CASL max_nosub_SPASS

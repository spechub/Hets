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

module SPASS.CreateDFGDoc where

import Data.Maybe

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Static.DevGraph

import Common.Lib.Pretty
import Common.Id
import Common.PrettyPrint
import Common.Result
import Common.GlobalAnnotations
import Common.AS_Annotation as AS_Anno
import Common.ProofUtils

import Syntax.AS_Library
import Syntax.Print_AS_Library ()

import CASL.Logic_CASL
import CASL.Sublogic

import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SPASS

import SPASS.Conversions
import SPASS.Translate
import SPASS.Sign
import SPASS.Print (genSPASSProblem)

spassConsTimeLimit :: Int
spassConsTimeLimit = 500

printDFG :: LIB_NAME -> SIMPLE_ID 
         -> Bool 
            -- ^ if True a conjecture false is added otherwise 
            -- its a theory without a conjecture.
         -> G_theory -> IO (Maybe Doc)
printDFG ln sn checkConsistency gth@(G_theory lid sign thSens) = 
    maybe (return Nothing)
          (\ (sign1,sens1) ->
               do prob <- genSPASSProblem 
                              thName
                              (spLogicalPart sign1 sens1)
                              (if checkConsistency
                               then Just falseConj
                               else Nothing)
                  return $ Just $ printText0 emptyGlobalAnnos $ 
                         (prob {settings = flags}))
 
      (if lessSublogicComor (sublogicOfTh gth) $ Comorphism idCASL
       then resultToMaybe  
             (coerceBasicTheory lid CASL "" (sign,sens)
              >>= map_theory idCASL
              >>= map_theory CASL2SubCFOL
              >>= map_theory SuleCFOL2SoftFOL)
       else if lessSublogicComor (sublogicOfTh gth) $ 
                Comorphism idCASL_nosub
            then resultToMaybe  
                     (coerceBasicTheory lid CASL "" (sign,sens)
                      >>= map_theory idCASL_nosub
                      >>= map_theory CASL2PCFOL
                      >>= map_theory CASL2SubCFOL
                      >>= map_theory SuleCFOL2SoftFOL)
            else Nothing)


  where sens = toNamedList thSens
        thName = showPretty (getLIB_ID ln) "_" ++ showPretty sn ""

        spLogicalPart sig sen = 
                            foldl insertSentence 
                                  (signToSPLogicalPart sig) 
                                  (reverse $ 
                                   prepareSenNames transSenName sen)

        flags = if checkConsistency
                then [SPFlag "TimeLimit" (show spassConsTimeLimit)
                     ,SPFlag "DocProof" "1"]
                else []

        falseConj = (emptyName falseSen) { senName = "inconsistent"
                                         , AS_Anno.isAxiom = False}

        falseSen = SPSimpleTerm SPFalse

        max_nosub_SPASS = 
               top {cons_features =
                        (cons_features top) {emptyMapping = True} }
        max_sub_SPASS = top { sub_features = LocFilSub
                               , cons_features = 
                                   (cons_features top) {onlyInjConstrs=False}}
        idCASL = IdComorphism CASL max_sub_SPASS
        idCASL_nosub = IdComorphism CASL max_nosub_SPASS
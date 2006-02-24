{- |
Module      :  $Header$
Description :  Generating DFG Doc out of SPASS theories.
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-protable(Logic)

Dumping a G_theory to DFG Doc.

-}

module SPASS.CreateDFGDoc where

import Data.Maybe

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce
import Static.DevGraph

import qualified Common.Lib.Map as Map
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
import Comorphisms.KnownProvers

import SPASS.Logic_SPASS
import SPASS.Conversions
import SPASS.Translate
import SPASS.Sign
import SPASS.Print (genSPASSProblem)

spassConsTimeLimit :: Int
spassConsTimeLimit = 500

printDFG :: LIB_NAME -> SIMPLE_ID 
         -> Bool 
            -- ^ if True a conjecture false is added otherwise 
            -- its a theory without conjecture.
         -> G_theory -> IO (Maybe Doc)
printDFG ln sn checkConsistency (G_theory lid sign thSens) =
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
 
      (case spassCMS of 
       Comorphism cid -> 
        do th <- coerceBasicTheory lid (sourceLogic cid) "" (sign,sens)
           th1 <- resultToMaybe $ map_theory cid th
           coerceBasicTheory (targetLogic cid) SPASS "" th1)

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
        falseConj = (emptyName falseSen) { senName = "consistent"
                                         , AS_Anno.isAxiom = False}
        falseSen = SPSimpleTerm SPFalse
        max_sub_SPASS = top {sub_features = LocFilSub}
        spassCMS = fromJust $ findComorphism (G_sublogics CASL max_sub_SPASS)
                                             knSPASSCms
        knSPASSCms = fromJust $ do knProvers <- resultToMaybe $ knownProvers
                                   Map.lookup "SPASS" knProvers
        
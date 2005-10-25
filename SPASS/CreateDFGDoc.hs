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
import Common.ProofUtils
import Syntax.AS_Library

import CASL.Logic_CASL
import CASL.Sublogic
import Comorphisms.KnownProvers

import SPASS.Logic_SPASS
import SPASS.Conversions
import SPASS.Translate
import SPASS.Sign
import SPASS.Print ()


printDFG :: LIB_NAME -> SIMPLE_ID -> G_theory -> Maybe Doc
printDFG ln sn (G_theory lid sign thSens) =
    case spassCMS of 
    Comorphism cid -> 
        do th <- coerceBasicTheory lid (sourceLogic cid) "" (sign,sens)
           th1 <- resultToMaybe $ map_theory cid th
           (sign1,sens1) <- coerceBasicTheory (targetLogic cid) SPASS "" th1
           return $ printText0 emptyGlobalAnnos $ problem sign1 sens1

  where sens = toNamedList thSens
        problem sig sen = 
            let iden = reverse (takeWhile (/= '/') $ reverse $ show ln)
                          ++ "_" ++ showPretty sn "" in
             SPProblem {identifier = iden,
                        description = SPDescription {name = "iden",
                                                     author = "hets user",
                                                     SPASS.Sign.version = 
                                                         Nothing,
                                                     logic = Nothing,
                                                     status = SPStateUnknown,
                                                     desc = "",
                                                     date = Nothing},
                        logicalPart = 
                            foldl insertSentence 
                                  (signToSPLogicalPart sig) 
                                  (reverse $ 
                                   prepareSenNames transSenName sen) }

        max_sub_SPASS = top {sub_features = LocFilSub}
        spassCMS = fromJust $ findComorphism (G_sublogics CASL max_sub_SPASS)
                                             knSPASSCms
        knSPASSCms = fromJust $ do knProvers <- resultToMaybe $ knownProvers
                                   Map.lookup "SPASS" knProvers
        
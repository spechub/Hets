{-# LANGUAGE CPP #-}
{- |
Module      :  ./Comorphisms/KnownProvers.hs
Description :  provides a map of provers to their most useful composed
  comorphisms
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

This module provides a map of provers to their most useful composed
comorphisms.
-}

module Comorphisms.KnownProvers
  ( KnownProversMap
  , KnownConsCheckersMap
  , defaultGUIProver
  , knownProversGUI
  , knownProversWithKind
  , shrinkKnownProvers
  , showKnownProvers
  , showAllKnownProvers
  , isaComorphisms
  ) where

import qualified Data.Map as Map

import System.Exit (exitFailure)

import Common.Result

import Logic.Logic (provers, AnyLogic (Logic), top_sublogic, language_name) -- hiding (top)
import Logic.Coerce ()
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover (proverName, hasProverKind, ProverKind (..))

import CASL.Logic_CASL
import CASL.Sublogic

import Comorphisms.QBF2Prop
import Comorphisms.Prop2QBF
import Comorphisms.Prop2CASL
--import Comorphisms.HPropNoms2CASL -- TODO: remove import
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.CommonLogic2IsabelleHOL
import Comorphisms.CSMOF2CASL
#ifdef CASLEXTENSIONS
import Comorphisms.HPAR2CASL
import Comorphisms.CoCASL2CoPCFOL
import Comorphisms.CoCASL2CoSubCFOL
import Comorphisms.CoCFOL2IsabelleHOL
import Comorphisms.Modal2CASL
import Comorphisms.CASL_DL2CASL
import Comorphisms.Maude2CASL
import Comorphisms.CommonLogic2CASL
import CommonLogic.Sublogic (folsl)
import Comorphisms.Adl2CASL
import CspCASL.Comorphisms
-- hybrid
import Comorphisms.Hybrid2CASL
#endif
#ifndef NOOWLLOGIC
import OWL2.OWL22CASL
#endif
import Comorphisms.PCoClTyConsHOL2PairsInIsaHOL
import Comorphisms.HasCASL2PCoClTyConsHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
#endif
import Comorphisms.SuleCFOL2TPTP
import Comorphisms.LogicList

import Comorphisms.DynComorphismList

type KnownProversMap = Map.Map String [AnyComorphism]
type KnownConsCheckersMap = Map.Map String [AnyComorphism]

-- | the default prover selected in the GUI
defaultGUIProver :: String
defaultGUIProver = "SPASS"

-- | a map of known prover names implemanting a GUI interface
knownProversGUI :: Result KnownProversMap
knownProversGUI = knownProversWithKind ProveGUI

idComorphisms :: [AnyComorphism]
idComorphisms = map (\ (Logic lid) ->
   Comorphism $ mkIdComorphism lid $ top_sublogic lid) logicList

{- | a map of known prover names for a specific prover kind
to a list of simple (composed) comorphisms -}
knownProversWithKind :: ProverKind -> Result KnownProversMap
knownProversWithKind pk =
    do isaCs <- isaComorphisms
       spassCs <- spassComorphisms
       qCs <- quickCheckComorphisms
       return $ foldl insProvers Map.empty
         $ idComorphisms ++ isaCs ++ spassCs ++ qCs
#ifdef CASLEXTENSIONS
              ++ [Comorphism cspCASLTrace]
#endif
       where insProvers kpm cm =
              case cm of
                Comorphism cid ->
                 let prs = provers (targetLogic cid)
                 in foldl (\ m p -> if hasProverKind pk p
                                    then Map.insertWith (flip (++))
                                          (proverName p) [cm] m
                                    else m) kpm prs

shrinkKnownProvers :: G_sublogics -> KnownProversMap -> KnownProversMap
shrinkKnownProvers sub = Map.filter (not . null) .
                         Map.map (filter $ lessSublogicComor sub)

isaComorphisms :: Result [AnyComorphism]
isaComorphisms = do
       -- CASL
       subpc2IHOLviaHasCASL <-
           compComorphism (Comorphism CASL2PCFOL) (Comorphism CASL2HasCASL)
           >>= ( \ x -> compComorphism x
                 $ Comorphism PCoClTyConsHOL2PairsInIsaHOL)
       subpc2IHOL <-
           compComorphism (Comorphism CASL2PCFOL)
               (Comorphism defaultCASL2SubCFOL)
           >>= ( \ x -> compComorphism x $ Comorphism CFOL2IsabelleHOL)
       -- HasCASL
       subHasCASL <-
           compComorphism (Comorphism HasCASL2PCoClTyConsHOL)
                          $ Comorphism PCoClTyConsHOL2PairsInIsaHOL
#ifdef CASLEXTENSIONS
       -- CoCASL
       casl_dl2CASL <- compComorphism (Comorphism CASL_DL2CASL) subpc2IHOL
       co2IHOL <-
           compComorphism (Comorphism CoCASL2CoPCFOL)
                              (Comorphism CoCASL2CoSubCFOL)
            >>= (\ x -> compComorphism x (Comorphism CoCFOL2IsabelleHOL))
       -- ModalCASL
       mod2IHOL <- compComorphism (Comorphism Modal2CASL) subpc2IHOL
       maude2IHOL <- compComorphism (Comorphism Maude2CASL) subpc2IHOL
       commonlogic2IHOL <-
           compComorphism (Comorphism $ CL2CFOL folsl) subpc2IHOL
#endif
#ifndef NOOWLLOGIC
       owl2HOL <- compComorphism (Comorphism OWL22CASL) subpc2IHOL
#endif
       -- Propositional
       prop2IHOL <- compComorphism (Comorphism Prop2CASL) subpc2IHOL
       return
         [ Comorphism CFOL2IsabelleHOL
         , Comorphism CommonLogic2IsabelleHOL
         , Comorphism QBF2Prop
         , Comorphism Prop2QBF
         , subpc2IHOLviaHasCASL
         , subpc2IHOL
#ifdef CASLEXTENSIONS
         , co2IHOL
         , mod2IHOL
         , maude2IHOL
         , casl_dl2CASL
         , commonlogic2IHOL
#endif
#ifdef PROGRAMATICA
         , Comorphism Haskell2IsabelleHOLCF
#endif
#ifndef NOOWLLOGIC
         , owl2HOL
#endif
         , subHasCASL
         , Comorphism PCoClTyConsHOL2PairsInIsaHOL
         , prop2IHOL ]

spassComorphisms :: Result [AnyComorphism]
spassComorphisms =
    do let max_nosub_SPASS =
               caslTop {cons_features = emptyMapConsFeature}
           max_sub_SPASS = max_nosub_SPASS { sub_features = LocFilSub }
           idCASL_sub = Comorphism (mkIdComorphism CASL max_sub_SPASS)
           idCASL_nosub = Comorphism (mkIdComorphism CASL max_nosub_SPASS)
           compSPASS x = compComorphism x (Comorphism suleCFOL2TPTP) 
                         -- use translation to TPTP instead of one to SoftFOL
       partOut <- compComorphism idCASL_sub (Comorphism defaultCASL2SubCFOL)
                   >>= compSPASS
       partSubOut <- compComorphism (Comorphism CASL2PCFOL)
                                     (Comorphism defaultCASL2SubCFOL)
                      >>= compComorphism idCASL_nosub
                      >>= compSPASS
       csmof2casl <- compSPASS (Comorphism CSMOF2CASL)
#ifdef CASLEXTENSIONS
-- hybrid
       --hpropnoms2SPASS <- compSPASS $ Comorphism HPropNoms2CASL
       hpar2SPASS <- compSPASS $ Comorphism HPAR2CASL
       hybr2SPASS <- compComorphism (Comorphism Hybrid2CASL) partOut
       prop2SPASS <- compComorphism (Comorphism Prop2CASL) partOut
       casl_dl2SPASS <- compComorphism (Comorphism CASL_DL2CASL) partOut
       maude2SPASS <- compComorphism (Comorphism Maude2CASL) partOut
       commonlogic2SPASS <- compComorphism (Comorphism $ CL2CFOL folsl)
         partOut
       adl2SPASS <- compSPASS (Comorphism Adl2CASL)
#endif
#ifndef NOOWLLOGIC
       owl2spass <- compComorphism (Comorphism OWL22CASL) partOut
#endif
       {- Fixme: constraint empty mapping is not available after Modal2CASL
       mod2SPASS <- compComorphism (Comorphism Modal2CASL) partSubOut
       CommonLogic -}
       dynSpassList <- mapM compSPASS
                       $ filter (\(Comorphism cid) -> let tLid = targetLogic cid in language_name tLid == "CASL")
                       dynComorphismList
       return $
         [ Comorphism suleCFOL2TPTP
         , partOut
         , partSubOut
#ifdef CASLEXTENSIONS
         --, hpropnoms2SPASS
         , hpar2SPASS
         , prop2SPASS
         , casl_dl2SPASS
         , maude2SPASS
         , commonlogic2SPASS
         , csmof2casl
         , adl2SPASS
-- hybrid
         , hybr2SPASS
#endif
#ifndef NOOWLLOGIC
         , owl2spass
#endif
         ] ++ dynSpassList

quickCheckComorphisms :: Result [AnyComorphism]
quickCheckComorphisms = do
   c <- compComorphism (Comorphism CASL2PCFOL)
                       (Comorphism defaultCASL2SubCFOL)
   return [c, Comorphism $ mkIdComorphism CASL
                                (top {has_part = False})]

showAllKnownProvers :: IO ()
showAllKnownProvers =
    do let Result ds mkpMap = knownProversGUI
       putStrLn "Diagnoses:"
       putStrLn $ unlines $ map show ds
       maybe exitFailure showKnownProvers mkpMap

showKnownProvers :: KnownProversMap -> IO ()
showKnownProvers km =
    do putStrLn "-----------\nKnownProvers:"
       putStrLn $ unlines $ map form $ Map.toList km
    where form (name, cl) =
              name ++ concatMap (("\n       " ++) . show) cl

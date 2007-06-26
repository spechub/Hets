{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

This module provides a map of provers to their most useful composed
comorphisms.
-}

module Comorphisms.KnownProvers (KnownProversMap,
                                 defaultGUIProver,
                                 knownProversGUI,
                                 knownProversWithKind,
                                 shrinkKnownProvers,
                                 showKnownProvers,
                                 showAllKnownProvers) where

import qualified Data.Map as Map

import System.Exit (exitFailure)

import Common.Result

import Logic.Logic (provers) -- hiding (top)
import Logic.Coerce()
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover (prover_name,hasProverKind,ProverKind(..))

import CASL.Logic_CASL
import CASL.Sublogic
import qualified Propositional.Sublogic as PS

import SoftFOL.Logic_SoftFOL (SoftFOL(..))
import Isabelle.Logic_Isabelle (Isabelle(..))
import qualified Propositional.Logic_Propositional as Prop

#ifdef UNI_PACKAGE
import Comorphisms.Prop2Prop
#endif
import Comorphisms.Prop2CASL
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.CFOL2IsabelleHOL
#ifdef CASLEXTENSIONS
import Comorphisms.CoCASL2CoPCFOL
import Comorphisms.CoCASL2CoSubCFOL
import Comorphisms.CoCFOL2IsabelleHOL
import Comorphisms.Modal2CASL
#endif
import Comorphisms.PCoClTyConsHOL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
#endif
import Comorphisms.CASL2SoftFOL

type KnownProversMap = Map.Map String [AnyComorphism]

-- | the default prover selected in the GUI
defaultGUIProver :: String
defaultGUIProver = "SPASS"

-- | a map of known prover names implemanting a GUI interface
knownProversGUI :: Result KnownProversMap
knownProversGUI = knownProversWithKind ProveGUI

-- | a map of known prover names for a specific prover kind
-- to a list of simple (composed) comorphisms
knownProversWithKind :: ProverKind -> Result KnownProversMap
knownProversWithKind pk =
    do isaCs <- isaComorphisms
       spassCs <- spassComorphisms
       zchaffCS <- zchaffComorphisms
       return $ foldl insProvers Map.empty (isaCs++spassCs++zchaffCS)
       where insProvers kpm cm =
              case cm of
              (Comorphism cid) ->
                 let prs = provers (targetLogic cid)
                 in foldl (\ m p -> if hasProverKind pk p
                                    then Map.insertWith mergeLists
                                          (prover_name p) [cm] m
                                    else m) kpm prs
             mergeLists xs ys = ys++xs


shrinkKnownProvers :: G_sublogics -> KnownProversMap -> KnownProversMap
shrinkKnownProvers sub = Map.filter (not . null) .
                         Map.map (filter (lessSublogicComor sub))

isaComorphisms :: Result [AnyComorphism]
isaComorphisms = do
       -- CASL
       subpc2IHOLviaHasCASL <-
           compComorphism (Comorphism CASL2PCFOL) (Comorphism CASL2HasCASL)
           >>= ( \ x -> compComorphism x
                 $ Comorphism PCoClTyConsHOL2IsabelleHOL)
       subpc2IHOL <-
           compComorphism (Comorphism CASL2PCFOL) (Comorphism CASL2SubCFOL)
           >>= ( \ x -> compComorphism x $ Comorphism CFOL2IsabelleHOL)
#ifdef CASLEXTENSIONS
       -- CoCASL
       co2IHOL <-
           compComorphism (Comorphism CoCASL2CoPCFOL)
                              (Comorphism CoCASL2CoSubCFOL)
            >>= (\ x -> compComorphism x (Comorphism CoCFOL2IsabelleHOL))
       -- ModalCASL
       mod2IHOL <- compComorphism (Comorphism Modal2CASL) subpc2IHOL
#endif
       -- Propositional
       prop2IHOL <- compComorphism (Comorphism Prop2CASL) subpc2IHOL
       return [Comorphism (IdComorphism Isabelle ()),
               Comorphism CFOL2IsabelleHOL, subpc2IHOLviaHasCASL, subpc2IHOL,
#ifdef CASLEXTENSIONS
               co2IHOL, mod2IHOL,
#endif
#ifdef PROGRAMATICA
               Comorphism Haskell2IsabelleHOLCF,
#endif
               Comorphism PCoClTyConsHOL2IsabelleHOL,
               prop2IHOL ]

spassComorphisms :: Result [AnyComorphism]
spassComorphisms =
    do let caslTop :: CASL_Sublogics
           caslTop = top
           max_nosub_SPASS =
               caslTop {cons_features =
                        (cons_features caslTop) {emptyMapping = True} }
           max_sub_SPASS = max_nosub_SPASS { sub_features = LocFilSub }
           idCASL_sub = Comorphism (IdComorphism CASL max_sub_SPASS)
           idCASL_nosub = Comorphism (IdComorphism CASL max_nosub_SPASS)
           compSPASS x = compComorphism x (Comorphism SuleCFOL2SoftFOL)
       partOut <- (compComorphism idCASL_sub (Comorphism CASL2SubCFOL)
                   >>= compSPASS)
       partSubOut <- (compComorphism (Comorphism CASL2PCFOL)
                                     (Comorphism CASL2SubCFOL)
                      >>= (compComorphism idCASL_nosub)
                      >>= compSPASS)
       prop2SPASS <- compComorphism (Comorphism Prop2CASL) partOut
       -- Fixme: constraint empty mapping is not available after Modal2CASL
       -- mod2SPASS <- compComorphism (Comorphism Modal2CASL) partSubOut
       return [Comorphism (IdComorphism SoftFOL ()),
               Comorphism SuleCFOL2SoftFOL,partOut,partSubOut,
              prop2SPASS]

zchaffComorphisms :: Result [AnyComorphism]
zchaffComorphisms = return
                    [
                     Comorphism (IdComorphism Prop.Propositional PS.top)
#ifdef UNI_PACKAGE
                    ,Comorphism Prop2CNF
#endif
                    ]

showAllKnownProvers :: IO ()
showAllKnownProvers =
    do let Result ds mkpMap = knownProversGUI
       putStrLn "Diagnoses:"
       putStrLn $ unlines $ map show ds
       maybe exitFailure showKnownProvers mkpMap

showKnownProvers :: KnownProversMap -> IO ()
showKnownProvers km =
    do putStrLn "-----------\nKnownProvers:"
       putStrLn $ unlines $ map form $ Map.toList $ km
    where form (name,cl) =
              name ++ concatMap (\c -> "\n       "++show c) cl

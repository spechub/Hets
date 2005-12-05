{-# OPTIONS -cpp #-}
{-| 
   
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
                                 knownProvers,
                                 shrinkKnownProvers,
                                 showKnownProvers) where

import Data.Maybe 
import Control.Monad

import qualified Common.Lib.Map as Map

import Common.Result

import Logic.Logic hiding (top)
import Logic.Coerce
import Logic.Grothendieck
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic

import Comorphisms.PCFOL2CFOL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.CASL2PCFOL
#ifdef CASLEXTENSIONS
import Comorphisms.CoCASL2CoPCFOL
import Comorphisms.CoPCFOL2CoCFOL
import Comorphisms.CoCFOL2IsabelleHOL
import Comorphisms.Modal2CASL
#endif
import Comorphisms.HasCASL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
#endif
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2SPASS

type KnownProversMap = Map.Map String [AnyComorphism]

-- | a map of known prover names to a list of simple (composed) comorphisms
knownProvers :: Result KnownProversMap
knownProvers = 
    do isaCs <- isaComorphisms
       spassCs <- spassComorphisms
       return (Map.fromList [("Isabelle", isaCs),
                             ("SPASS", spassCs)])

shrinkKnownProvers :: G_sublogics -> KnownProversMap -> KnownProversMap
shrinkKnownProvers sub = Map.filter (not . null) . 
                         Map.map (filter (lessSublogicComor sub))

isaComorphisms :: Result [AnyComorphism]
isaComorphisms = do
       -- CASL
       pc2IHOL <- compComorphism (Comorphism PCFOL2CFOL) 
                                 (Comorphism CFOL2IsabelleHOL)
       subpc2IHOL <- compComorphism (Comorphism CASL2PCFOL) pc2IHOL
#ifdef CASLEXTENSIONS
       -- CoCASL
       co2IHOL <- 
           (compComorphism (Comorphism CoCASL2CoPCFOL)
                           (Comorphism CoPCFOL2CoCFOL)
            >>= (\x -> compComorphism x (Comorphism CoPCFOL2CoCFOL)))
       -- ModalCASL
       mod2IHOL <- compComorphism (Comorphism Modal2CASL) subpc2IHOL
#endif
       return [Comorphism CFOL2IsabelleHOL, pc2IHOL, subpc2IHOL,
#ifdef CASLEXTENSIONS
               co2IHOL, mod2IHOL,
#endif
#ifdef PROGRAMATICA
               Comorphism Haskell2IsabelleHOLCF,
#endif
               Comorphism HasCASL2IsabelleHOL]

spassComorphisms :: Result [AnyComorphism]
spassComorphisms = 
    do let max_sub_SPASS = top { sub_features = LocFilSub
                               , cons_features = 
                                   (cons_features top) {onlyInjConstrs=False} }
           idCASL =  Comorphism (IdComorphism CASL max_sub_SPASS)
       partOut <- (compComorphism idCASL (Comorphism CASL2SubCFOL) 
                   >>= (\x -> compComorphism x (Comorphism CASL2SPASS)))
       -- mod2SPASS <- compComorphism (Comorphism Modal2CASL) partOut
       return [Comorphism CASL2SPASS,partOut]

showAllKnownProvers :: IO ()
showAllKnownProvers = 
    do let Result ds mkpMap = knownProvers
       putStrLn "Diagnosises:"
       putStrLn $ unlines $ map show ds
       maybe (return ()) showKnownProvers mkpMap

showKnownProvers :: KnownProversMap -> IO ()
showKnownProvers km =
    do putStrLn "-----------\nKnownProvers:"
       putStrLn $ unlines $ map form $ Map.toList $ km
    where form (name,cl) =
              name ++ concatMap (\c -> "\n       "++show c) cl


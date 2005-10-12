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

module Comorphisms.KnownProvers (KnownProversMap, knownProvers) where

import Data.Maybe 
import Control.Monad

import qualified Common.Lib.Map as Map

import Common.Result

import Logic.Grothendieck

import Comorphisms.PCFOL2CFOL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.CASL2PCFOL
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

isaComorphisms :: Result [AnyComorphism]
isaComorphisms = 
    do partOut <- compComorphism (Comorphism PCFOL2CFOL) 
                                 (Comorphism CFOL2IsabelleHOL)
       sub_partOut <- compComorphism (Comorphism CASL2PCFOL)
                                     partOut
       return [Comorphism CFOL2IsabelleHOL,partOut,sub_partOut]

spassComorphisms :: Result [AnyComorphism]
spassComorphisms = 
    do --partOut <- compComorphism (Comorphism CASL2SubCFOL) 
       --                          (Comorphism CASL2SPASS)
       return [Comorphism CASL2SPASS{-,partOut-}]

showKnownProvers :: IO ()
showKnownProvers = 
    do let Result ds mkpMap = knownProvers
       putStrLn "Diagnosises:"
       putStrLn $ unlines $ map show ds
       putStrLn "-----------\nKnownProvers:"
       when (isJust mkpMap) 
            (putStrLn $ unlines $ map form $ Map.toList $ fromJust mkpMap)
    where form (name,cl) =
              name ++ concatMap (\c -> "\n       "++show c) cl
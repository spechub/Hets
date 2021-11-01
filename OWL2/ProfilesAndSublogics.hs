{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/ProfilesAndSublogics.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

OWL2 Profiles (EL, QL and RL) + OWL2 complexity analysis

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.ProfilesAndSublogics where

import OWL2.AS
import OWL2.Profiles
import OWL2.Sublogic
import OWL2.Sign
import OWL2.Morphism

import Data.Data

data ProfSub = ProfSub
    { profiles :: Profiles
    , sublogic :: OWLSub
    } deriving (Show, Eq, Ord, Typeable, Data)

allProfSubs :: [[ProfSub]]
allProfSubs = map (map (`ProfSub` slBottom)) allProfiles
  ++ map (map (ProfSub topProfile)) allSublogics

bottomS :: ProfSub
bottomS = ProfSub topProfile slBottom

topS :: ProfSub
topS = ProfSub bottomProfile slTop

maxS :: ProfSub -> ProfSub -> ProfSub
maxS ps1 ps2 = ProfSub (andProfileList [profiles ps1, profiles ps2])
    (slMax (sublogic ps1) (sublogic ps2))

nameS :: ProfSub -> String
nameS ps = printProfile (profiles ps) ++ "-" ++ slName (sublogic ps)

psAxiom :: Axiom -> ProfSub
psAxiom ax = ProfSub (axiom ax) (slAxiom ax)

sSig :: Sign -> ProfSub
sSig s = bottomS {sublogic = slSig s}

sMorph :: OWLMorphism -> ProfSub
sMorph m = bottomS {sublogic = slMor m}

prSign :: ProfSub -> Sign -> Sign
prSign s = prSig (sublogic s)

prMorph :: ProfSub -> OWLMorphism -> OWLMorphism
prMorph s a = a
    { osource = prSign s $ osource a
    , otarget = prSign s $ otarget a }

prOntDoc :: ProfSub -> OntologyDocument -> OntologyDocument
prOntDoc ps = prODoc (sublogic ps)

profilesAndSublogic :: OntologyDocument -> ProfSub
profilesAndSublogic odoc = ProfSub (ontologyProfiles odoc) (slODoc odoc)

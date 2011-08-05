{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 Profiles (EL, QL and RL) + OWL2 DL

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.ProfilesAndSublogics
    ( ProfSub (..)
    , Profiles (..)
    , topS
    , bottomS
    , maxS
    , nameS
    , psAxiom
    , profilesAndSublogic
    , sSig
    , sMorph
    , prODoc
    , prSig
    , prMorph
    ) where

import OWL2.MS
import OWL2.Profiles
import OWL2.Sublogic
import OWL2.Sign
import OWL2.Morphism

data ProfSub = ProfSub {
        profiles :: Profiles,
        sublogic :: OWLSub
    } deriving (Show, Eq, Ord)

bottomS :: ProfSub
bottomS = ProfSub topProfile sl_bottom

topS :: ProfSub
topS = ProfSub bottomProfile sl_top

maxS :: ProfSub -> ProfSub -> ProfSub
maxS ps1 ps2 = ProfSub (andProfileList [profiles ps1, profiles ps2])
                (sl_max (sublogic ps1) (sublogic ps2))

nameS :: ProfSub -> String
nameS ps = printProfile (profiles ps) ++ "-" ++ sl_name (sublogic ps)

psAxiom :: Axiom -> ProfSub
psAxiom ax = ProfSub (axiom ax) (slAxiom ax)

sSig :: Sign -> ProfSub
sSig s = bottomS {sublogic = sl_sig s}

sMorph :: OWLMorphism -> ProfSub
sMorph m = bottomS {sublogic = sl_mor m}

prSig :: ProfSub -> Sign -> Sign
prSig s = pr_sig (sublogic s)

prMorph :: ProfSub -> OWLMorphism -> OWLMorphism
prMorph s a = a
    { osource = prSig s $ osource a
    , otarget = prSig s $ otarget a }

prODoc :: ProfSub -> OntologyDocument -> OntologyDocument
prODoc ps = pr_o_doc (sublogic ps)

profilesAndSublogic :: OntologyDocument -> ProfSub
profilesAndSublogic odoc = ProfSub (ontologyProfiles odoc) (sl_o_doc odoc)

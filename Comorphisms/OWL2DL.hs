{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to DL
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a not yet implemented comorphism
-}

module Comorphisms.OWL2DL where

import Logic.Logic
import Logic.Comorphism

--OWL = domain
import OWL.Logic_OWL11
import OWL.AS
import OWL.Sign as OWL

--DL = codomain
import DL.Logic_DL
import DL.AS
import DL.Sign as DL

import Common.AS_Annotation
import Common.Result
import Common.Id

import Text.XML.HXT.DOM.QualifiedName (QName(..))

data OWL2DL = OWL2DL deriving Show

instance Language OWL2DL

instance Comorphism
    OWL2DL     -- comorphism
    OWL11           -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    Sentence        -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OWL.Sign        -- signature domain
    OWL11_Morphism  -- morphism domain
    ()              -- symbol domain
    ()              -- rawsymbol domain
    ATP_ProofTree   -- proof tree codomain
    DL         -- lid codomain
    ()                     -- Sublogics
    DLBasic                -- basic_spec
    DLBasicItem            -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    DL.Sign                -- sign
    DLMorphism             -- morphism
    DLSymbol               -- symbol
    RawDLSymbol            -- raw_symbol
    ()                     -- proof_tree
    where
      sourceLogic OWL2DL    = OWL11
      sourceSublogic OWL2DL = ()
      targetLogic OWL2DL    = DL
      mapSublogic OWL2DL _  = Just ()
      map_theory OWL2DL = mapTheory
      map_morphism = mapDefaultMorphism

qNameToId :: QName -> Id
qNameToId = stringToId . localPart

mapTheory :: (OWL.Sign, [Named Sentence])
          -> Result (DL.Sign, [Named DLBasicItem])
mapTheory = error "map_theory OWL2DL"


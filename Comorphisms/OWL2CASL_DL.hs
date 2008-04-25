{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to CASL_Dl
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a not yet implemented comorphism
-}

module Comorphisms.OWL2CASL_DL where

import Logic.Logic
import Logic.Comorphism

--OWL = domain
import OWL.Logic_OWL11
import OWL.AS
import OWL.Sign as OS

--CASL_DL = codomain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.StatAna -- DLSign
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

data OWL2CASL_DL = OWL2CASL_DL deriving Show

instance Language OWL2CASL_DL

instance Comorphism
    OWL2CASL_DL     -- comorphism
    OWL11           -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    Sentence        -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OS.Sign         -- signature domain
    OWL11_Morphism  -- morphism domain
    ()              -- symbol domain
    ()              -- rawsymbol domain
    ATP_ProofTree   -- proof tree codomain
    CASL_DL         -- lid codomain
    ()              -- sublogics codomain
    DL_BASIC_SPEC   -- Basic spec codomain
    DLFORMULA       -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    DLSign          -- signature codomain
    DLMor           -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ()              -- proof tree domain
    where
      sourceLogic OWL2CASL_DL    = OWL11
      sourceSublogic OWL2CASL_DL = ()
      targetLogic OWL2CASL_DL    = CASL_DL
      mapSublogic OWL2CASL_DL _  = Just ()
      map_theory OWL2CASL_DL = error "map_theory OWL2CASL_DL"
      map_morphism OWL2CASL_DL = error "map_morphism OWL2CASL_DL"

-- Primary concepts stay in OWL, but non-primary concepts cannot be
-- superconcepts of primary ones

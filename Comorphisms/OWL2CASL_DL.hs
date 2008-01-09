{- |
Module      :  Comorphisms/OWL2CASL_DL.hs
Description :  Comorphism from OWL 1.1 to CASL_Dl
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

-}

module Comorphisms.OWL2CASL_DL where

import Logic.Logic
import Logic.Comorphism
import Common.Id()
import qualified Data.Set as Set()
import qualified Common.Lib.Rel as Rel()
import qualified Data.Map as Map()
import Common.AS_Annotation
import Data.List()
import Common.Result
import CASL_DL.PredefinedCASLAxioms()

--OWL = domain
import OWL.Logic_OWL11
import OWL.AS
import qualified OWL.Sign as OS
import OWL.Sign

--CASL_DL = codomain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.Sign()
import CASL_DL.StatAna -- DLSign
import CASL_DL.PredefinedSign()
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
    ()              -- proof tree codomain
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
      mapSublogic OWL2CASL_DL _  = Nothing
      map_theory  OWL2CASL_DL    = trTheory
      map_morphism OWL2CASL_DL   = trMor

trTheory :: (OS.Sign, [Named Sentence]) -> Result (DLSign, [Named DLFORMULA])
trTheory _ = error "NYI"

trMor :: OWL11_Morphism -> Result DLMor
trMor _ = error "NYI"

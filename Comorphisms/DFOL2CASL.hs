module Comorphisms.DFOL2CASL where

import Logic.Logic
import Logic.Comorphism

import Common.ProofTree

import DFOL.Logic_DFOL
import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import DFOL.Symbol
import DFOL.Comorphism

import qualified CASL.Logic_CASL as CASL_Logic
import qualified CASL.Sublogic as CASL_Sublogic
import qualified CASL.AS_Basic_CASL as CASL_AS
import qualified CASL.Sign as CASL_Sign
import qualified CASL.Morphism as CASL_Morphism

-- cid for the comorphism
data DFOL2CASL = DFOL2CASL deriving Show

instance Language DFOL2CASL where
   language_name DFOL2CASL = "DFOL2CASL"

instance Comorphism DFOL2CASL
   DFOL () BASIC_SPEC FORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        Sign Morphism Symbol Symbol ()
   CASL_Logic.CASL CASL_Sublogic.CASL_Sublogics CASL_Logic.CASLBasicSpec
        CASL_AS.CASLFORMULA CASL_AS.SYMB_ITEMS CASL_AS.SYMB_MAP_ITEMS
        CASL_Sign.CASLSign CASL_Morphism.CASLMor CASL_Sign.Symbol
        CASL_Morphism.RawSymbol ProofTree
   where
   sourceLogic DFOL2CASL = DFOL
   sourceSublogic DFOL2CASL = ()
   targetLogic DFOL2CASL = CASL_Logic.CASL
   mapSublogic DFOL2CASL () = Just CASL_Sublogic.caslTop
   map_theory DFOL2CASL = wrapInResult . theoryTransl
   map_symbol DFOL2CASL = error "map symbol nyi"
   map_sentence DFOL2CASL = \ sig -> wrapInResult . (senTransl sig)
   map_morphism DFOL2CASL = wrapInResult . morphTransl
   has_model_expansion DFOL2CASL = True

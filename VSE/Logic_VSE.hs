{-# OPTIONS -fallow-undecidable-instances -w #-}
{- |
Module      :  $Header$
Description :  the incomplete Logic instance for VSE
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

morphisms and symbols need to be extended, too
-}

module VSE.Logic_VSE where

import qualified Data.Map as Map
import Common.Id
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import VSE.As
import VSE.ATC_VSE ()
import Logic.Logic

data VSE = VSE deriving Show

instance Language VSE where
 description _ =
  "VSE extends CASL by modal operators and programs."

type VSEBasicSpec = BASIC_SPEC Procdefs Procdecls Dlformula
type Procs = Map.Map Id Profile
type VSESign = Sign Dlformula Procs
type VSEMor = Morphism Dlformula Procs ()

instance Category VSESign VSEMor

instance Syntax VSE VSEBasicSpec SYMB_ITEMS SYMB_MAP_ITEMS

instance Sentences VSE Sentence VSESign VSEMor Symbol where
      parse_sentence VSE = Nothing
      sym_of VSE = symOf
      symmap_of VSE = morphismToSymbMap
      sym_name VSE = symName

instance StaticAnalysis VSE VSEBasicSpec Sentence
               SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol where
         stat_symb_map_items VSE = statSymbMapItems
         stat_symb_items VSE = statSymbItems
         ensures_amalgamability VSE _ =
             fail "VSE: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec VSE _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw VSE = symbolToRaw
         id_to_raw VSE = idToRaw

instance Logic VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
         stability _ = Unstable
         empty_proof_tree _ = ()

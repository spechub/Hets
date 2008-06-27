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

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.MapSentence
import CASL.SymbolMapAnalysis
import CASL.Parse_AS_Basic
import CASL.SymbolParser
import CASL.SimplifySen

import VSE.As
import VSE.Parse
import VSE.Ana
import VSE.ATC_VSE ()
import Logic.Logic
import CASL.Logic_CASL ()

data VSE = VSE deriving Show

instance Language VSE where
 description _ =
  "VSE extends CASL by modal operators and programs."

type VSEBasicSpec = BASIC_SPEC () Procdecls Dlformula
type VSESign = Sign Dlformula Procs
type VSEMor = Morphism Dlformula Procs ()

instance Syntax VSE VSEBasicSpec SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec VSE = Just $ basicSpec reservedWords
    parse_symb_items VSE = Just $ symbItems reservedWords
    parse_symb_map_items VSE = Just $ symbMapItems reservedWords

instance Sentences VSE Sentence VSESign VSEMor Symbol where
      map_sen VSE m = return . mapSen mapDlformula m
      parse_sentence VSE = Nothing
      sym_of VSE = symOf
      symmap_of VSE = morphismToSymbMap
      sym_name VSE = symName
      simplify_sen VSE = simplifySen minExpForm simpDlformula

interSigM :: Monad m => (e -> e -> m e) -> Sign f e -> Sign f e -> m (Sign f e)
interSigM f a b = do
  e <- f (extendedInfo a) $ extendedInfo b
  return $ interSig (const $ const e) a b

instance StaticAnalysis VSE VSEBasicSpec Sentence
               SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol where
         basic_analysis VSE = Just $ basicAna
         stat_symb_map_items VSE = statSymbMapItems
         stat_symb_items VSE = statSymbItems
         ensures_amalgamability VSE _ =
             fail "VSE: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec VSE _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw VSE = symbolToRaw
         id_to_raw VSE = idToRaw
         matches VSE = CASL.Morphism.matches

         empty_signature VSE = emptySign emptyProcs
         signature_union VSE = addSigM unionProcs
         intersection VSE = interSigM interProcs
         morphism_union VSE = morphismUnionM (const id) unionProcs
         final_union VSE = addSigM unionProcs
         inclusion VSE = sigInclusion () isSubProcsMap diffProcs
         cogenerated_sign VSE s = fmap correctTarget
           . cogeneratedSign () isSubProcsMap s
         generated_sign VSE s = fmap correctTarget
           . generatedSign () isSubProcsMap s
         induced_from_morphism VSE rm = fmap correctTarget
           . inducedFromMorphism () isSubProcsMap rm
         induced_from_to_morphism VSE rm s1 = fmap correctTarget
           . inducedFromToMorphism () isSubProcsMap diffProcs rm s1

instance Logic VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
         stability _ = Unstable
         empty_proof_tree _ = ()

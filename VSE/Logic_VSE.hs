{-# LANGUAGE CPP, MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  the incomplete Logic instance for VSE
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

morphisms and symbols need to be extended, too
-}

module VSE.Logic_VSE where

import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.MapSentence
import CASL.SymbolMapAnalysis
import CASL.Parse_AS_Basic
import CASL.Qualify
import CASL.SymbolParser
import CASL.SimplifySen
import CASL.ToDoc
import CASL.Logic_CASL () -- instance Category VSESign VSEMor
import CASL.ColimSign

import VSE.As
import VSE.Parse
import VSE.Ana
import VSE.ATC_VSE ()
#ifdef UNI_PACKAGE
import VSE.Prove (vse)
#endif
import Logic.Logic

import qualified Data.Map as Map

data VSE = VSE deriving Show

instance Language VSE where
 description _ =
  "VSE extends CASL by modal operators and programs."

instance SignExtension Procs where
  isSubSignExtension = isSubProcsMap

instance Syntax VSE VSEBasicSpec SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec VSE = Just $ basicSpec reservedWords
    parse_symb_items VSE = Just $ symbItems reservedWords
    parse_symb_map_items VSE = Just $ symbMapItems reservedWords

instance Sentences VSE Sentence VSESign VSEMor Symbol where
      map_sen VSE m = return . mapSen mapDlformula m
      sym_of VSE = symOf
      symmap_of VSE = morphismToSymbMap
      sym_name VSE = symName
      simplify_sen VSE = simplifySen minExpForm simpDlformula
      print_named VSE = printTheoryFormula
      print_sign VSE sig = let e = extendedInfo sig in
        pretty sig { opMap = diffOpMapSet (opMap sig) $ procsToOpMap e
                   , predMap = diffMapSet (predMap sig) $ procsToPredMap e }

interSigM :: Monad m => (e -> e -> m e) -> Sign f e -> Sign f e -> m (Sign f e)
interSigM f a b = do
  e <- f (extendedInfo a) $ extendedInfo b
  return $ interSig (const $ const e) a b

instance StaticAnalysis VSE VSEBasicSpec Sentence
               SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol where
         basic_analysis VSE = Just basicAna
         stat_symb_map_items VSE _ _ = statSymbMapItems
         stat_symb_items VSE _ = statSymbItems
         signature_colimit VSE diag =
           let (sig, mmor) = signColimit diag extVSEColimit
           in return (correctSign sig, Map.map correctTarget mmor)
         qualify VSE = qualifySigExt inducedExt emptyMorExt
         symbol_to_raw VSE = symbolToRaw
         id_to_raw VSE = idToRaw
         matches VSE = CASL.Morphism.matches

         empty_signature VSE = emptySign emptyProcs
         signature_union VSE = addSigM unionProcs
         intersection VSE = interSigM interProcs
         morphism_union VSE = morphismUnionM retExtMap unionProcs
         final_union VSE = addSigM unionProcs
         is_subsig VSE = isSubSig isSubProcsMap
         subsig_inclusion VSE = sigInclusion emptyMorExt
         cogenerated_sign VSE s = fmap correctTarget
           . cogeneratedSign emptyMorExt s
         generated_sign VSE s = fmap correctTarget
           . generatedSign emptyMorExt s
         induced_from_morphism VSE rm = fmap correctTarget
           . inducedFromMorphismExt inducedExt (constMorphExt emptyMorExt) rm
         induced_from_to_morphism VSE rm s1 = fmap correctTarget
           . inducedFromToMorphismExt inducedExt (constMorphExt emptyMorExt)
             (\ _ _ -> return emptyMorExt) isSubProcsMap diffProcs rm s1

instance Logic VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
         stability VSE = Unstable
#ifdef UNI_PACKAGE
         provers VSE = [vse]
#endif

{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./RigidCASL/Logic_RigidCASL.hs
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module RigidCASL.Logic_RigidCASL where

import Logic.Logic
import RigidCASL.AS_Rigid
import RigidCASL.Sign
import RigidCASL.Morphism
import RigidCASL.ATC_RigidCASL ()
import RigidCASL.Parse_AS ()
import RigidCASL.Print_AS
import RigidCASL.StaticAna
import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.SimplifySen
import CASL.ToDoc
import CASL.Logic_CASL ()
import Common.Keywords (rigidS)
import qualified Common.Lib.Rel as Rel
import qualified Data.Set as Set

data RigidCASL = RigidCASL deriving Show

instance Language RigidCASL where
 description _ = "RigidCASL\n" ++
                 "Extends CASL with rigid symbols."

instance Syntax RigidCASL R_BASIC_SPEC Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec RigidCASL = Just $ basicSpec [rigidS]
    parse_symb_items RigidCASL = undefined -- Just $ symbItems [rigidS]
    parse_symb_map_items RigidCASL = undefined -- Just $ symbMapItems hybrid_reserved_words

-- Important convention: we use CASL syntax for quantifiers but variables are rigid! 
-- This must be taken into account when writing translations.

instance Sentences RigidCASL CASLFORMULA RSign RigidMor Symbol where
      map_sen RigidCASL = undefined -- return . mapSen map_H_FORMULA h
      sym_of RigidCASL = symOf -- this loses rigidity information
      symmap_of RigidCASL = undefined --morphismToSymbMap
      sym_name RigidCASL = symName
      simplify_sen RigidCASL = simplifyCASLSen
      print_sign RigidCASL sig = printSign printRigidExt $ 
                                   sig {sortRel = Rel.difference (Rel.transReduce $ sortRel sig)
                                                  . Rel.transReduce $ Rel.fromSet $
                                                  Set.map (\x->(x,x)) $ rigidSorts $ extendedInfo sig,
                                        opMap = diffOpMapSet (opMap sig) $ rigidOps $ extendedInfo sig,
                                        predMap = diffMapSet (predMap sig) $ rigidPreds $ extendedInfo sig}
      print_named RigidCASL = printTheoryFormula

instance StaticAnalysis RigidCASL R_BASIC_SPEC CASLFORMULA
        SYMB_ITEMS SYMB_MAP_ITEMS
        RSign
        RigidMor
        Symbol RawSymbol where
                basic_analysis RigidCASL = Just basicRigidAnalysis
                stat_symb_map_items RigidCASL = statSymbMapItems
                stat_symb_items RigidCASL = statSymbItems
                symbol_to_raw RigidCASL = symbolToRaw
                id_to_raw RigidCASL = idToRaw
                matches RigidCASL = CASL.Morphism.matches
                empty_signature RigidCASL = emptySign emptyRigidExt
                signature_union RigidCASL s = return . addSig addRigidExt s
                intersection RigidCASL s = return . interSig interRigidExt s
                morphism_union RigidCASL = undefined --plainMorphismUnion (addSig addRigidExt)
                final_union RigidCASL = undefined --finalUnion (addSig addRigidExt)
                is_subsig RigidCASL = isSubSig isSubRigidExt
                subsig_inclusion RigidCASL = undefined -- sigInclusion emptyMorExt
                cogenerated_sign RigidCASL = undefined --cogeneratedSign emptyMorExt
                generated_sign RigidCASL = undefined -- generatedSign emptyMorExt
                induced_from_morphism RigidCASL = undefined -- inducedFromMorphism emptyMorExt
                induced_from_to_morphism RigidCASL = undefined --inducedFromToMorphism
                 -- emptyMorExt isSubRigidExt diffRigidExt
                theory_to_taxonomy RigidCASL = undefined --convTaxo

instance Logic RigidCASL ()
        R_BASIC_SPEC CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        RSign
        RigidMor
        Symbol RawSymbol () where
                stability _ = Experimental
                empty_proof_tree _ = ()

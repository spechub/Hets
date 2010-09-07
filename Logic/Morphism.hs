{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveDataTypeable
  , FlexibleInstances, UndecidableInstances, IncoherentInstances
  , ExistentialQuantification, GeneralizedNewtypeDeriving #-}
{- |
Module      :  $Header$
Description :  interface (type class) for logic projections (morphisms) in Hets
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic)

Interface (type class) for logic projections (morphisms) in Hets

Provides data structures for institution morphisms.
   These are just collections of
   functions between (some of) the types of logics.
-}

{-   References: see Logic.hs

   Todo:
   morphism modifications / representation maps
-}

module Logic.Morphism where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import Data.Typeable
import ATerm.Lib -- (ShATermConvertible)
import Common.DocUtils
import Common.AS_Annotation
import Common.Id

class (Language cid,
       Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 sign_symbol1 symbol1 proof_tree1,
       Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 sign_symbol2 symbol2 proof_tree2) =>
  Morphism cid
    lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 sign_symbol1 symbol1 proof_tree1
    lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
         sign2 morphism2 sign_symbol2 symbol2 proof_tree2
    | cid -> lid1, cid -> lid2
    , lid1 -> sublogics1 basic_spec1 sentence1 symb_items1
        symb_map_items1 sign1 morphism1 sign_symbol1 symbol1 proof_tree1
    , lid2 -> sublogics2 basic_spec2 sentence2 symb_items2
        symb_map_items2 sign2 morphism2 sign_symbol2 symbol2 proof_tree2
  where
    -- source and target logic and sublogic
    -- the source sublogic is the maximal one for which the comorphism works
    -- the target sublogic is the resulting one
    morSourceLogic :: cid -> lid1
    morSourceSublogic :: cid -> sublogics1
    morTargetLogic :: cid -> lid2
    morTargetSublogic :: cid -> sublogics2
    -- finer information of target sublogics corresponding to source sublogics
    morMapSublogicSign :: cid -> sublogics1 -> sublogics2
    -- information about the source sublogics corresponding to target sublogics
    morMapSublogicSen :: cid -> sublogics2 -> sublogics1
    -- the translation functions are partial
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Maybe basic_spec2
    -- we do not cover theoroidal morphisms,
    --   since there are no relevant examples and they do not compose nicely
    -- no mapping of theories, since signatures and sentences are mapped
    --   contravariantly
    morMap_sign :: cid -> sign1 -> Maybe sign2
    morMap_morphism :: cid -> morphism1 -> Maybe morphism2
    morMap_sentence :: cid -> sign1 -> sentence2 -> Maybe sentence1
          -- also covers semi-morphisms ??
          -- with no sentence translation
          -- - but these are spans!
    morMap_sign_symbol :: cid -> sign_symbol1 -> Set.Set sign_symbol2
    -- morConstituents not needed, because composition only via lax triangles

-- | identity morphisms
data IdMorphism lid sublogics =
    IdMorphism lid sublogics deriving (Typeable, Show)

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism sign_symbol symbol proof_tree =>
         Language (IdMorphism lid sublogics) where
           language_name (IdMorphism lid sub) = "id_" ++ language_name lid
               ++ case sublogicName sub of
                    [] -> ""
                    h -> '.' : h

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism sign_symbol symbol proof_tree =>
         Morphism (IdMorphism lid sublogics)
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism sign_symbol symbol proof_tree
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism sign_symbol symbol proof_tree
         where
           morSourceLogic (IdMorphism lid _sub) = lid
           morTargetLogic (IdMorphism lid _sub) = lid
           morSourceSublogic (IdMorphism _lid sub) = sub
           morTargetSublogic (IdMorphism _lid sub) = sub
           --changed to identities!
           morMapSublogicSign _ x = x
           morMapSublogicSen _ x = x
           morMap_sign _ = Just
           morMap_morphism _ = Just
           morMap_sentence _ _ = Just
           morMap_sign_symbol _ = Set.singleton

-- composition not needed, use lax triangles instead

-- | comorphisms inducing morphisms
class Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2 =>
      InducingComorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2
  where
    indMorMap_sign :: cid -> sign2 -> Maybe sign1
    indMorMap_morphism :: cid -> morphism2 -> Maybe morphism1
    epsilon :: cid -> sign2 -> Maybe morphism2

--------------------------------------------------------------------------

-- Morphisms as spans of comorphisms


--    if the morphism is (psi, alpha, beta) : I -> J
--    it is replaced with the following span
--    SignI    id     ->     SignI         psi ->        SignJ
--    SenI     alpha  <-     psi;SenJ      id  ->        psi;SenJ
--    ModI     beta   ->     psi^op;ModJ   id  <-        psi^op;ModJ

--    1. introduce a new logic for the domain of the span
--       this logic will have
--         * the name (SpanDomain cid) where cid is the name of the morphism
--         * sublogics - pairs (s1, s2) with s1 being a sublogic of I and s2
-- being a sublogic of J; the lattice is the product lattice of the two
-- existing lattices
--         * basic_spec will be () - the unit type, because we mix signatures
-- with sentences in specifications
--         * sentence - sentences of J, wrapped
--         * symb_items - ()
--         * symb_map_items - ()
--         * sign - signatures of I
--         * morphism - morphisms of I
--         * sign_symbol - sign_symbols of I
--         * symbol - symbols of I
--         * proof_tree - proof_tree of J

data SpanDomain cid = SpanDomain cid deriving (Eq, Show)

data SublogicsPair a b = SublogicsPair a b deriving (Eq, Ord, Show, Typeable)

instance Language cid => Language (SpanDomain cid) where
  language_name (SpanDomain cid) = "SpanDomain" ++ language_name cid

{- the category of signatures is exactly the category of signatures of
the sublogic on which the morphism is defined, but with another name -}

instance Morphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2
         => Syntax (SpanDomain cid) () () ()
-- default is ok

newtype S2 s = S2 { sentence2 :: s }
  deriving (Eq, Ord, Show, Typeable, ShATermConvertible, Pretty)

instance GetRange s => GetRange (S2 s) where
  getRange (S2 s) = getRange s
  rangeSpan (S2 s) = rangeSpan s

instance Morphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2
    => Sentences (SpanDomain cid) (S2 sentence2) sign1 morphism1
       sign_symbol1 where

--one has to take care about signature and morphisms
--and translate them to targetLogic
--we get a Maybe sign/morphism

 map_sen (SpanDomain cid) mor1 (S2 sen) =
                        case morMap_morphism cid mor1 of
                           Just mor2 -> fmap S2 $
                               map_sen (morTargetLogic cid) mor2 sen
                           Nothing -> statFail (SpanDomain cid) "map_sen"
 simplify_sen (SpanDomain cid) sigma (S2 sen) =
                       case morMap_sign cid sigma of
                          Just sigma2 -> S2 $
                              simplify_sen (morTargetLogic cid) sigma2 sen
                          Nothing -> error "simplify_sen"
 print_named (SpanDomain cid) = print_named (morTargetLogic cid)
     . mapNamed sentence2
 sym_of (SpanDomain cid) = sym_of (morSourceLogic cid)
 symmap_of (SpanDomain cid) = symmap_of (morSourceLogic cid)
 sym_name (SpanDomain cid) = sym_name (morSourceLogic cid)

instance (Morphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2)
        => StaticAnalysis (SpanDomain cid) () (S2 sentence2) () ()
           sign1 morphism1 sign_symbol1 symbol1 where
 ensures_amalgamability l _ = statFail l "ensures_amalgamability"
 symbol_to_raw (SpanDomain cid) = symbol_to_raw (morSourceLogic cid)
 id_to_raw (SpanDomain cid) = id_to_raw (morSourceLogic cid)
 matches (SpanDomain cid) = matches (morSourceLogic cid)
 empty_signature (SpanDomain cid) = empty_signature (morSourceLogic cid)
 signature_union (SpanDomain cid) = signature_union (morSourceLogic cid)
 final_union (SpanDomain cid) = final_union (morSourceLogic cid)
 morphism_union (SpanDomain cid) = morphism_union (morSourceLogic cid)
 is_subsig (SpanDomain cid) = is_subsig (morSourceLogic cid)
 subsig_inclusion (SpanDomain cid) = subsig_inclusion (morSourceLogic cid)
 generated_sign (SpanDomain cid) = generated_sign (morSourceLogic cid)
 cogenerated_sign (SpanDomain cid) = cogenerated_sign (morSourceLogic cid)
 is_transportable (SpanDomain cid) = is_transportable (morSourceLogic cid)
 is_injective (SpanDomain cid) = is_injective (morSourceLogic cid)

instance (SemiLatticeWithTop sublogics1, SemiLatticeWithTop sublogics2)
         => SemiLatticeWithTop (SublogicsPair sublogics1 sublogics2) where
            top = SublogicsPair top top
            join (SublogicsPair x1 y1) (SublogicsPair x2 y2) =
                SublogicsPair (join x1 x2) (join y1 y2)

instance (SemiLatticeWithTop sublogics1, MinSublogic sublogics2 sentence2)
  => MinSublogic (SublogicsPair sublogics1 sublogics2) (S2 sentence2) where
  minSublogic (S2 sen2) = SublogicsPair top (minSublogic sen2)

{- just a dummy implementation, it should be the sublogic of sen2 in J
paired with its image through morMapSublogicSen? -}

instance (MinSublogic sublogics1 alpha, SemiLatticeWithTop sublogics2)
         => MinSublogic (SublogicsPair sublogics1 sublogics2) alpha where
  minSublogic x = SublogicsPair (minSublogic x) top

{- also should have instances of MinSublogic class for Sublogics-pair
and morphism1, sign_symbol1, sign1 this is why the wrapping is needed -}

-- instance SemiLatticeWithTop sublogics => MinSublogic sublogics () where
--     minSublogic _ = top

instance (MinSublogic sublogics1 alpha, SemiLatticeWithTop sublogics2)
          => ProjectSublogic (SublogicsPair sublogics1 sublogics2) alpha where
      projectSublogic _ x = x
-- it should be used for (), morphism1, sign_symbol1, sign1

instance (MinSublogic sublogics1 sign1, SemiLatticeWithTop sublogics2)
         => ProjectSublogicM (SublogicsPair sublogics1 sublogics2) sign1 where
      projectSublogicM _ = Just

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (SublogicsPair a b) where
  toShATermAux att0 (SublogicsPair a b) = do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "SublogicsPair" [a',b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "SublogicsPair" [a,b] _ ->
      case fromShATerm' a att0 of { (att1, a') ->
      case fromShATerm' b att1 of { (att2, b') ->
      (att2, SublogicsPair a' b') }}
    u -> fromShATermError "SublogicsPair" u

instance (SublogicName sublogics1, SublogicName sublogics2)
    => SublogicName (SublogicsPair sublogics1 sublogics2) where
       sublogicName (SublogicsPair sub1 sub2) =
           let s1 = sublogicName sub1
               s2 = sublogicName sub2
           in if null s1 then s2 else if null s2 then s1 else
              s1 ++ "|" ++ s2

instance ( MinSublogic sublogics1 ()
         , Morphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 sign_symbol1 symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 sign_symbol2 symbol2 proof_tree2
         ) => Logic (SpanDomain cid) (SublogicsPair sublogics1 sublogics2) ()
          (S2 sentence2) () () sign1 morphism1 sign_symbol1 symbol1 proof_tree2
    where
      stability (SpanDomain _) = Experimental
      data_logic (SpanDomain _) = Nothing
      top_sublogic (SpanDomain cid) = SublogicsPair
        (top_sublogic $ morSourceLogic cid) $ top_sublogic $ morTargetLogic cid
      all_sublogics (SpanDomain cid) =
          [ SublogicsPair x y
          | x <- all_sublogics (morSourceLogic cid)
          , y <- all_sublogics (morTargetLogic cid) ]
      -- project_sublogic_epsilon - default implementation for now
      provers _ = []
      cons_checkers _ = []
      conservativityCheck _ = []
      empty_proof_tree (SpanDomain cid) = empty_proof_tree (morTargetLogic cid)

-- * Morphisms

-- | Existential type for morphisms
data AnyMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Morphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Morphism cid

{-
instance Eq AnyMorphism where
  Morphism cid1 == Morphism cid2 =
     constituents cid1 == constituents cid2
  -- need to be refined, using morphism translations !!!
-}

instance Show AnyMorphism where
  show (Morphism cid) = language_name cid
    ++ " : " ++ language_name (morSourceLogic cid)
    ++ " -> " ++ language_name (morTargetLogic cid)

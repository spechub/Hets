
-- needs ghc -fglasgow-exts -package data

{- HetCATS/Comorphism.hs
   $Id$
   Till Mossakowski, Christian Maeder
   
   Provides data structures logic (co)morphisms. 
   Logic (co)morphisms are just collections of
   functions between (some of) the types of logics.

   References: see Logic.hs

   Todo:
   Weak amalgamability, also for comorphisms
   comorphism maps
   comorphisms out of sublogic relationships
-}

module Logic.Comorphism where

import Logic.Logic
import Common.Lib.Set
import Data.Maybe(catMaybes)
import Data.Dynamic

import Common.ATerm.Lib
--import Logic.Grothendieck
-- Logic comorphisms (possibly also morphisms via adjointness)


class (Language cid, Typeable cid,
       Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
       Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
             | cid -> lid1, cid -> lid2, 
               cid -> sublogics1, cid -> basic_spec1, cid -> sentence1, 
               cid -> symb_items1, cid -> symb_map_items1, cid -> sign1, 
               cid -> morphism1, cid -> symbol1, cid -> raw_symbol1, 
               cid -> proof_tree1, cid -> sublogics2, cid -> basic_spec2, 
               cid -> sentence2, cid -> symb_items2, 
               cid -> symb_map_items2, cid -> sign2, cid -> morphism2, 
               cid -> symbol2, cid -> raw_symbol2, cid -> proof_tree2
  where
    sourceLogic :: cid -> lid1
    sourceSublogic :: cid -> sublogics1
    targetLogic :: cid -> lid2
    targetSublogic :: cid -> sublogics2
    -- the translation functions are partial 
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Maybe basic_spec2
    -- cover theoroidal comorphisms as well
    map_sign :: cid -> sign1 -> Maybe (sign2,[sentence2])
    map_morphism :: cid -> morphism1 -> Maybe morphism2
    map_sentence :: cid -> sign1 -> sentence1 -> Maybe sentence2
          -- also covers semi-comorphisms
          -- with no sentence translation
          -- - but these are spans!
    map_symbol :: cid -> symbol1 -> Set symbol2
    fromShATerm_sign1 :: (ATermConvertible sign) => cid -> ATermTable -> sign
    fromShATerm_sign1 cid att = fromShATerm att
    fromShATerm_morphism2 :: (ATermConvertible morphism) => cid -> ATermTable -> morphism
    fromShATerm_morphism2 cid att = fromShATerm att


data IdComorphism lid  = 
     IdComorphism lid deriving Show
idComorphismTc :: TyCon
idComorphismTc = mkTyCon "Logic.Comorphism.IdComorphism"
instance Typeable (IdComorphism lid) where 
  typeOf s = mkAppTy idComorphismTc []
                --[typeOf ((undefined :: IdComorphism a -> a) s)]

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Language (IdComorphism lid) where
           language_name _ = "id_"++language_name (error "Comorphism.hs"::lid)

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Comorphism (IdComorphism lid) --sublogics
          --basic_spec sentence symb_items symb_map_items
          --sign morphism symbol raw_symbol proof_tree)
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree 
         where
           sourceLogic (IdComorphism lid) = lid
           targetLogic (IdComorphism lid) = lid
           sourceSublogic _ = top
           targetSublogic _ = top
           map_sign _ = \sigma -> Just(sigma,[])
           map_morphism _ = Just
           map_sentence _ = \_ -> Just
           map_symbol _ = single


data (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) =>
     CompComorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1 
            cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3 = 
     CompComorphism cid1 cid2 deriving (Show)
tyconCompComorphism :: TyCon
tyconCompComorphism = mkTyCon "Logic.Comorphism.CompComorphism"
instance Typeable (CompComorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) where
  typeOf _ = mkAppTy tyconCompComorphism []



instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => Language (CompComorphism cid1
              lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              cid2
              lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
              lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) where
   language_name (CompComorphism cid1 cid2) = 
     language_name cid1++";"
     ++language_name cid2

instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => Comorphism (CompComorphism cid1
              lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              cid2
              lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
              lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) 
              lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
              sign3 morphism3 symbol3 raw_symbol3 proof_tree3
             where
   sourceLogic (CompComorphism cid1 _) = 
     sourceLogic cid1
   targetLogic (CompComorphism _ cid2) = 
     targetLogic cid2
   sourceSublogic (CompComorphism cid1 _) = 
     sourceSublogic cid1
   targetSublogic (CompComorphism _ cid2) = 
     targetSublogic cid2
   map_sentence (CompComorphism cid1 cid2) = 
       \si1 se1 -> 
         do (si2,_) <- map_sign cid1 si1
            se2 <- map_sentence cid1 si1 se1 
            map_sentence cid2 si2 se2
   map_sign (CompComorphism cid1 cid2) = 
       \si1 -> 
         do (si2, se2s) <- map_sign cid1 si1
            (si3, se3s) <- map_sign cid2 si2 
            return (si3, se3s ++ catMaybes
                          (map (map_sentence cid2 si2) se2s))

   map_morphism (CompComorphism cid1 cid2) = \ m1 -> map_morphism cid1 m1 
                             >>=  map_morphism cid2

   map_symbol (CompComorphism cid1 cid2) = \ s1 -> unions
		(map (map_symbol cid2) 
                 (toList (map_symbol cid1 s1)))
 

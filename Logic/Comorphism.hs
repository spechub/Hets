
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

-- Logic comorphisms (possibly also morphisms via adjointness)


class (Language cid,
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
             | cid -> lid1, cid -> lid2
  where
    sourceLogic :: cid -> lid1
    source_sublogic :: cid -> sublogics1
    targetLogic :: cid -> lid2
    target_sublogic :: cid -> sublogics2
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


data IdComorphism lid  = 
     IdComorphism lid deriving Show

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Language (IdComorphism lid) where
           language_name _ = "id_"++language_name (undefined::lid)

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
           source_sublogic _ = top
           target_sublogic _ = top
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
tyconCompComorphism = mkTyCon "CompComorphism"
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
   source_sublogic (CompComorphism cid1 _) = 
     source_sublogic cid1
   target_sublogic (CompComorphism _ cid2) = 
     target_sublogic cid2
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
 

{-

idComorphism l = IdComorphism l (empty_as l)

instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Typeable (Comorphism lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)


instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Eq (Comorphism lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where
  r1==r2 = language_name r1 == language_name r2 &&
           language_name (source r1) == language_name (source r2) &&
           language_name (target r1) == language_name (target r2) &&
           coerce (source r1) (source r2) (source_sublogic r1) ==
             Just  (source_sublogic r2) &&
           coerce (target r1) (target r2) (target_sublogic r1) ==
             Just  (target_sublogic r2)

instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
    Show (Comorphism lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where
  show r = show (source r) ++ " -> " ++ show (target r)

id_comorphism :: 
     Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree => 
  lid -> 
    Comorphism lid sublogics basic_spec sentence symb_items symb_map_items
                  sign morphism symbol raw_symbol proof_tree
              lid sublogics basic_spec sentence symb_items symb_map_items
                  sign morphism symbol raw_symbol proof_tree
id_comorphism lid = 
     Comorphism {

-- composition of logic comorphisms (diagrammatic order)
comp_comorphism :: 
     (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
      Logic lid3 sublogics3
        basic_spec3 sentence3 symb_items3 symb_map_items3 
        sign3 morphism3 symbol3 raw_symbol3 proof_tree3
     ) =>
     Comorphism lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2

 ->  Comorphism lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3

 ->  Maybe (
     Comorphism lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3 )

comp_comorphism r1 r2 = if target_sublogic r1 <<= source_sublogic r2 then
   Just(Comorphism{ 
   language_name = language_name r1++";"++language_name r2,
   source = source r1, target = target r2,
   source_sublogic = source_sublogic r1, 
   target_sublogic = target_sublogic r2,
   map_sentence = 
       \si1 se1 -> 
         do (si2,_) <- map_sign r1 si1
            se2 <- map_sentence r1 si1 se1 
            map_sentence r2 si2 se2 ,
   map_sign = 
       \si1 -> 
         do (si2, se2s) <- map_sign r1 si1
            (si3, se3s) <- map_sign r2 si2 
            return (si3, se3s ++ catMaybes 
				  (map (map_sentence r2 si2) se2s)) ,

   projection = undefined ,

   map_morphism = \ m1 -> map_morphism r1 m1 >>=  map_morphism r2 ,

   map_symbol = \ s1 -> unions
		(map (map_symbol r2) (toList (map_symbol r1 s1)))
   }) else Nothing

-}
{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (via Logic)
   
   Provides data structures logic (co)morphisms. 
   Logic (co)morphisms are just collections of
   functions between (some of) the types of logics.

-}

{-   References: see Logic.hs

   Todo:
   Weak amalgamability, also for comorphisms
   comorphism modifications
   comorphisms out of sublogic relationships
   restrictions of comorphisms to sublogics
   morphisms and other translations via spans
-}

module Logic.Comorphism where

import Logic.Logic
import Common.Lib.Set
import Data.Maybe
import Data.Dynamic
import Common.AS_Annotation (Named, mapNamedM)

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
    -- source and target logic and sublogic
    -- the source sublogic is the maximal one for which the comorphism works
    -- the target sublogic is the resulting one
    sourceLogic :: cid -> lid1
    sourceSublogic :: cid -> sublogics1
    targetLogic :: cid -> lid2
    targetSublogic :: cid -> sublogics2
    -- finer information of target sublogics corresponding to source sublogics
    mapSublogic :: cid -> sublogics1 -> sublogics2
    -- default implementation
    mapSublogic cid _ = targetSublogic cid
    -- the translation functions are partial 
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Maybe basic_spec2
    -- cover theoroidal comorphisms as well
    map_sign :: cid -> sign1 -> Maybe (sign2,[Named sentence2])
    map_theory :: cid -> (sign1,[Named sentence1])
                      -> Maybe (sign2,[Named sentence2])
    --default implementations
    map_sign cid sign = map_theory cid (sign,[])
    map_theory cid (sign,sens) = do
       (sign',sens') <- map_sign cid sign
       let sens'' = mapMaybe (mapNamedM (map_sentence cid sign)) sens
       return (sign',sens'++sens'')
    map_morphism :: cid -> morphism1 -> Maybe morphism2
    map_sentence :: cid -> sign1 -> sentence1 -> Maybe sentence2
          -- also covers semi-comorphisms
          -- with no sentence translation
          -- - but these are spans!
    map_symbol :: cid -> symbol1 -> Set symbol2

data IdComorphism lid sublogics = 
     IdComorphism lid sublogics deriving Show
idComorphismTc :: TyCon
idComorphismTc = mkTyCon "Logic.Comorphism.IdComorphism"
instance Typeable (IdComorphism lid sub) where 
  typeOf _ = mkTyConApp idComorphismTc []

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Language (IdComorphism lid sublogics) where
           language_name (IdComorphism lid sub) = 
             "id_"++language_name lid++"."++show sub

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Comorphism (IdComorphism lid sublogics)
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree 
         where
           sourceLogic (IdComorphism lid sub) = lid
           targetLogic (IdComorphism lid sub) = lid
           sourceSublogic (IdComorphism lid sub) = sub
           targetSublogic (IdComorphism lid sub) = sub
           map_sign _ = \sigma -> Just(sigma,[])
           map_morphism _ = Just
           map_sentence _ = \_ -> Just
           map_symbol _ = single


data CompComorphism cid1 cid2 = CompComorphism cid1 cid2 deriving Show

tyconCompComorphism :: TyCon
tyconCompComorphism = mkTyCon "Logic.Comorphism.CompComorphism"
instance Typeable (CompComorphism cid1 cid2) where
  typeOf _ = mkTyConApp tyconCompComorphism []

instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => Language (CompComorphism cid1 cid2) where
   language_name (CompComorphism cid1 cid2) = 
     language_name cid1++";"
     ++language_name cid2


instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => Comorphism (CompComorphism cid1 cid2)
              lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
              sign3 morphism3 symbol3 raw_symbol3 proof_tree3 where
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
	    (si2', se2') <- coerce (targetLogic cid1) (sourceLogic cid2) 
			    (si2, se2)
            map_sentence cid2 si2' se2'
   map_sign (CompComorphism cid1 cid2) = 
       \si1 -> 
         do (si2, se2s) <- map_sign cid1 si1
            (si2', se2s') <- coerce (targetLogic cid1) (sourceLogic cid2) 
			     (si2, se2s)
            (si3, se3s) <- map_sign cid2 si2' 
            return (si3, se3s ++ catMaybes
                          (map (mapNamedM (map_sentence cid2 si2')) se2s'))

   map_theory (CompComorphism cid1 cid2) = 
       \ti1 -> 
         do ti2 <- map_theory cid1 ti1
            ti2' <- coerce (targetLogic cid1) (sourceLogic cid2) ti2 
            map_theory cid2 ti2'

   map_morphism (CompComorphism cid1 cid2) = \ m1 -> 
       do m2 <- map_morphism cid1 m1 
	  m3 <- coerce (targetLogic cid1) (sourceLogic cid2) m2
          map_morphism cid2 m3

   map_symbol (CompComorphism cid1 cid2) = \ s1 -> 
         let mycast = fromJust . coerce (targetLogic cid1) (sourceLogic cid2)
	 in unions
		(map (map_symbol cid2 . mycast) 
                 (toList (map_symbol cid1 s1)))

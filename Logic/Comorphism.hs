{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  central interface (type class) for logic translations (comorphisms) in Hets
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (via Logic)

Central interface (type class) for logic translations (comorphisms) in Hets
   These are just collections of
   functions between (some of) the types of logics.

   References: see Logic.hs
-}

module Logic.Comorphism where

import Logic.Logic
import Logic.Coerce
import qualified Data.Set as Set
import Common.Result
import Common.ProofUtils
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

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
    sourceLogic :: cid -> lid1
    sourceSublogic :: cid -> sublogics1
    targetLogic :: cid -> lid2
    -- finer information of target sublogics corresponding to source sublogics
    mapSublogic :: cid -> sublogics1 -> sublogics2
    -- the translation functions are partial
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Result basic_spec2
    -- cover theoroidal comorphisms as well
    map_theory :: cid -> (sign1,[Named sentence1])
                      -> Result (sign2,[Named sentence2])
    map_morphism :: cid -> morphism1 -> Result morphism2
    map_sentence :: cid -> sign1 -> sentence1 -> Result sentence2
          -- also covers semi-comorphisms
          -- with no sentence translation
          -- - but these are spans!
    map_symbol :: cid -> symbol1 -> Set.Set symbol2
    constituents :: cid -> [String]
    -- default implementation
    constituents cid = [language_name cid]

targetSublogic :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sublogics2
targetSublogic cid = mapSublogic cid $ sourceSublogic cid

-- | this function is base on 'map_theory' using no sentences as input
map_sign :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sign1 -> Result (sign2,[Named sentence2])
map_sign cid sign = wrapMapTheory cid (sign,[])

mapDefaultMorphism :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> morphism1 -> Result morphism2
mapDefaultMorphism cid mor = do
  let src = sourceLogic cid
  (sig1, _) <- map_sign cid $ dom src mor
  (sig2, _) <- map_sign cid $ cod src mor
  inclusion (targetLogic cid) sig1 sig2

failMapSentence :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sign1 -> sentence1 -> Result sentence2
failMapSentence cid _ _ =
    fail $ "Unsupported sentence translation " ++ show cid

errMapSymbol :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> symbol1 -> Set.Set symbol2
errMapSymbol cid _ = error $ "no symbol mapping for " ++ show cid

-- | use this function instead of 'map_theory'
wrapMapTheory :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            => cid -> (sign1, [Named sentence1])
                   -> Result (sign2, [Named sentence2])
wrapMapTheory cid (sign, sens) =
      case sourceSublogic cid of
        sub -> case minSublogic sign of
          sigLog -> case foldl join sigLog
                    $ map (minSublogic . sentence) sens of
            senLog ->
              if isSubElem senLog sub
                 then map_theory cid (sign, sens)
                 else fail $ "for '" ++ language_name cid ++
                           "' expected sublogic '" ++
                           concat (sublogic_names sub) ++
                           "'\n but found sublogic '" ++
                           concat (sublogic_names senLog) ++
                           "' with signature sublogic '" ++
                           concat (sublogic_names sigLog) ++ "'\n" ++
                 show (vcat $ pretty sign : map
                                (print_named $ sourceLogic cid) sens)

simpleTheoryMapping :: (sign1 -> sign2) -> (sentence1 -> sentence2)
                    -> (sign1, [Named sentence1])
                    -> (sign2, [Named sentence2])
simpleTheoryMapping mapSig mapSen (sign,sens) =
    (mapSig sign, map (mapNamed mapSen) sens)

mkTheoryMapping :: (Monad m) => (sign1 -> m (sign2, [Named sentence2]))
                   -> (sign1 -> sentence1 -> m sentence2)
                   -> (sign1, [Named sentence1])
                   -> m (sign2, [Named sentence2])
mkTheoryMapping mapSig mapSen (sign,sens) = do
       (sign',sens') <- mapSig sign
       sens'' <- mapM (mapNamedM $ mapSen sign) sens
       return (sign', disambiguateSens Set.empty . nameSens $ sens' ++ sens'')

data IdComorphism lid sublogics =
     IdComorphism lid sublogics

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
   Show (IdComorphism lid sublogics)
   where
   show = language_name

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Language (IdComorphism lid sublogics) where
           language_name (IdComorphism lid sub) =
               case sublogic_names sub of
               [] -> error "language_name IdComorphism"
               h : _ -> "id_" ++ language_name lid ++ "." ++ h

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
           sourceLogic (IdComorphism lid _sub) = lid
           targetLogic (IdComorphism lid _sub) = lid
           sourceSublogic (IdComorphism _lid sub) = sub
           mapSublogic _ = id
           map_theory _ = return
           map_morphism _ = return
           map_sentence _ = \_ -> return
           map_symbol _ = Set.singleton
           constituents _ = []

data CompComorphism cid1 cid2 = CompComorphism cid1 cid2 deriving Show

instance (Language cid1, Language cid2)
          => Language (CompComorphism cid1 cid2) where
   language_name (CompComorphism cid1 cid2) =
     language_name cid1++ ";" ++language_name cid2


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
   mapSublogic (CompComorphism cid1 cid2) =
     mapSublogic cid2
     . forceCoerceSublogic (targetLogic cid1) (sourceLogic cid2)
     . mapSublogic cid1
   map_sentence (CompComorphism cid1 cid2) =
       \si1 se1 ->
         do (si2,_) <- map_sign cid1 si1
            se2 <- map_sentence cid1 si1 se1
            (si2', se2') <- coerceBasicTheory
                (targetLogic cid1) (sourceLogic cid2)
                "Mapping sentence along comorphism" (si2, [emptyName se2])
            case se2' of
                [x] -> map_sentence cid2 si2' $ sentence x
                _ -> error "CompComorphism.map_sentence"

   map_theory (CompComorphism cid1 cid2) =
       \ti1 ->
         do ti2 <- map_theory cid1 ti1
            ti2' <- coerceBasicTheory (targetLogic cid1) (sourceLogic cid2)
                        "Mapping theory along comorphism" ti2
            wrapMapTheory cid2 ti2'

   map_morphism (CompComorphism cid1 cid2) = \ m1 ->
       do m2 <- map_morphism cid1 m1
          m3 <- coerceMorphism (targetLogic cid1) (sourceLogic cid2)
                  "Mapping signature morphism along comorphism"m2
          map_morphism cid2 m3

   map_symbol (CompComorphism cid1 cid2) = \ s1 ->
         let mycast = coerceSymbol (targetLogic cid1) (sourceLogic cid2)
         in Set.unions
                (map (map_symbol cid2 . mycast)
                 (Set.toList (map_symbol cid1 s1)))
   constituents (CompComorphism cid1 cid2) =
      constituents cid1 ++ constituents cid2

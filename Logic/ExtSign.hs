{- |
Module      :  $Header$
Description :  signatures with symbol sets
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Those functions that operate over signatures are extended to work over
signatures with symbol sets
-}

module Logic.ExtSign where

import qualified Data.Set as Set
import Common.Result
import Logic.Logic

data Ord symbol => ExtSign sign symbol = ExtSign
  { plainSign :: sign
  , nonImportedSymbols :: (Set.Set symbol)
  } deriving (Eq, Show)

mkExtSign :: Ord symbol => sign -> ExtSign sign symbol
mkExtSign s = ExtSign s Set.empty

ext_sym_of :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> Set.Set symbol
ext_sym_of l = sym_of l . plainSign

ext_ide :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> morphism
ext_ide l = ide l . plainSign

ext_empty_signature :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol)
ext_empty_signature l = mkExtSign (empty_signature l)

ext_signature_union :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> (ExtSign sign symbol)
               -> Result (ExtSign sign symbol)
ext_signature_union l (ExtSign s1 _) (ExtSign s2 _) =
    fmap mkExtSign $ signature_union l s1 s2

ext_signature_difference :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> (ExtSign sign symbol)
               -> Result (ExtSign sign symbol)
ext_signature_difference l (ExtSign s1 _) (ExtSign s2 _) =
    fmap mkExtSign $ signature_difference l s1 s2

ext_is_subsig :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> (ExtSign sign symbol) -> Bool
ext_is_subsig l (ExtSign sig1 _) (ExtSign sig2 _) =
    is_subsig l sig1 sig2

ext_final_union :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> (ExtSign sign symbol)
               -> Result (ExtSign sign symbol)
ext_final_union l (ExtSign s1 _) (ExtSign s2 _) =
    fmap mkExtSign $ final_union l s1 s2

ext_inclusion :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> (ExtSign sign symbol) -> (ExtSign sign symbol)
               -> Result morphism
ext_inclusion l (ExtSign s1 _) (ExtSign s2 _) =
    inclusion l s1 s2

ext_generated_sign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> Set.Set symbol -> (ExtSign sign symbol) -> Result morphism
ext_generated_sign l s (ExtSign sig _) =
    generated_sign l s sig

ext_cogenerated_sign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> Set.Set symbol -> (ExtSign sign symbol) -> Result morphism
ext_cogenerated_sign l s (ExtSign sig _) =
    cogenerated_sign l s sig

ext_induced_from_morphism :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> EndoMap raw_symbol -> (ExtSign sign symbol)
               -> Result morphism
ext_induced_from_morphism l r (ExtSign s _) =
    induced_from_morphism l r s

ext_induced_from_to_morphism :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> EndoMap raw_symbol -> (ExtSign sign symbol)
               -> (ExtSign sign symbol) -> Result morphism
ext_induced_from_to_morphism l r (ExtSign s1 _) (ExtSign s2 _) =
    induced_from_to_morphism l r s1 s2

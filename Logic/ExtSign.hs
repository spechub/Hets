{- |
Module      :  ./Logic/ExtSign.hs
Description :  derived functions for signatures with symbol sets
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Functions from the class Logic that operate over signatures are
extended to work over signatures with symbol sets.
-}

module Logic.ExtSign where

import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import Control.Monad
import Common.Result
import Common.DocUtils
import Common.ExtSign
import Logic.Logic
import Data.Hashable


ext_sym_of :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> Set.HashSet symbol
ext_sym_of l = symset_of l . plainSign

-- | simply put all symbols into the symbol set
makeExtSign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> sign -> ExtSign sign symbol
makeExtSign l s = ExtSign s $ symset_of l s

ext_ide :: (Ord symbol, Category sign morphism)
           => ExtSign sign symbol -> morphism
ext_ide = ide . plainSign

ext_empty_signature :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol
ext_empty_signature = mkExtSign . empty_signature

checkExtSign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> String -> ExtSign sign symbol -> Result ()
checkExtSign l msg e@(ExtSign s sy) = let sys = symset_of l s in
    unless (Set.isSubsetOf sy sys) $
        error $ "inconsistent symbol set in extended signature: " ++ msg ++ "\n"
             ++ showDoc e "\rwith unknown symbols\n"
             ++ showDoc (Set.difference sy sys) ""

ext_signature_union :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> ExtSign sign symbol
               -> Result (ExtSign sign symbol)
ext_signature_union l e1@(ExtSign s1 _) e2@(ExtSign s2 _) = do
    checkExtSign l "ext_signature_union_1" e1
    checkExtSign l "ext_signature_union_2" e2
    s <- signature_union l s1 s2
    return $ makeExtSign l s

ext_signature_intersect :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> ExtSign sign symbol
               -> Result (ExtSign sign symbol)
ext_signature_intersect l e1@(ExtSign s1 _) e2@(ExtSign s2 _) = do
    checkExtSign l "ext_signature_intersect_1" e1
    checkExtSign l "ext_signature_intersect_2" e2
    s <- intersection l s1 s2
    return $ makeExtSign l s

ext_is_subsig :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> ExtSign sign symbol -> Bool
ext_is_subsig l (ExtSign sig1 _) (ExtSign sig2 _) =
    is_subsig l sig1 sig2

ext_final_union :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> ExtSign sign symbol
               -> Result (ExtSign sign symbol)
ext_final_union l e1@(ExtSign s1 _) e2@(ExtSign s2 _) = do
    checkExtSign l "f1" e1
    checkExtSign l "f2" e2
    s <- final_union l s1 s2
    return $ makeExtSign l s

ext_inclusion :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> ExtSign sign symbol -> ExtSign sign symbol -> Result morphism
ext_inclusion l (ExtSign s1 _) (ExtSign s2 _) =
    inclusion l s1 s2

ext_generated_sign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> Set.HashSet symbol -> ExtSign sign symbol -> Result morphism
ext_generated_sign l s (ExtSign sig _) =
    generated_sign l s sig

ext_cogenerated_sign :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> Set.HashSet symbol -> ExtSign sign symbol -> Result morphism
ext_cogenerated_sign l s (ExtSign sig _) =
    cogenerated_sign l s sig

ext_induced_from_morphism :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> EndoMap raw_symbol -> ExtSign sign symbol
               -> Result morphism
ext_induced_from_morphism l rmap (ExtSign sigma _) = do
  -- first check: do all source raw symbols match with source signature?
  checkRawMap l rmap sigma
  mor <- induced_from_morphism l rmap sigma
  legal_mor mor
  return mor

checkRawMap :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> EndoMap raw_symbol -> sign -> Result ()
checkRawMap l rmap = checkRawSyms l (Map.keys rmap) . symset_of l

checkRawSyms :: Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        => lid -> [raw_symbol] -> Set.HashSet symbol -> Result ()
checkRawSyms l rsyms syms = do
  let unknownSyms = filter
          ( \ rsy -> Set.null $ Set.filter (flip (matches l) rsy) syms)
          rsyms
  unless (null unknownSyms)
    $ Result [mkDiag Error "unknown symbols" unknownSyms] $ Just ()

ext_induced_from_to_morphism :: (Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree, Hashable symbol)
        => lid -> EndoMap raw_symbol -> ExtSign sign symbol
               -> ExtSign sign symbol -> Result morphism
ext_induced_from_to_morphism l r s@(ExtSign p sy) t = do
    checkExtSign l "from" s
    checkExtSign l "to" t
    checkRawMap l r p
    checkRawSyms l (Map.elems r) $ nonImportedSymbols t
    mor <- induced_from_to_morphism l r s t
    let sysI = Set.toList $ Set.difference (symset_of l p) sy
        morM = symmap_of l mor
        msysI = map (\ sym -> Map.findWithDefault sym sym morM) sysI
    unless (sysI == msysI)
      $ fail $ "imported symbols are mapped differently.\n"
            ++ showDoc (filter (uncurry (/=)) $ zip sysI msysI) ""
    legal_mor mor
    return mor

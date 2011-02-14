{- |
Module      :  $Header$
Description :  Functions for defining LF as a logical framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Framework where

import LF.Sign
import LF.Morphism

import Framework.WriteLogicUtils

import Data.List

baseB :: BASE
baseB = "Framework/specs/logics/propositional/syntax/base.elf"

baseM :: MODULE
baseM = "Base"

o :: Symbol
o = Symbol baseB baseM "o"

ded :: Symbol
ded = Symbol baseB baseM "ded"

baseSig :: Sign
baseSig = Sign baseB baseM
             [ Def o Type Nothing
             , Def ded (Func [Const o] Type) Nothing ]

sen_type_symbol :: Symbol
sen_type_symbol = o

-----------------------------------------------------------------
-----------------------------------------------------------------

writeLogic :: String -> String
writeLogic l =
  let basic_specC = "BASIC_SPEC"
      symb_itemsC = "SYMB_ITEMS"
      symb_map_itemsC = "SYMB_MAP_ITEMS"
      signC = "Sign"      
      sentenceC = "Sentence"
      morphismC = "Morphism"
      symbolC = "Symbol"
      raw_symbolC = "RAW_SYM"
      sublogicsC = "()"
      proof_treeC = "()"
      ml = "LF"
      
      -- module declaration
      comp_opt = mkCompOpt [multiOpt,synOpt]
      mod_decl = mkModDecl $ l ++ "." ++ "Logic_" ++ l
      
      -- imports
      impts1 = mkImports ["Logic.Logic"]
      impts2 = mkImports ["LF.AS", "LF.Sign", "LF.Morphism",
                          "LF.Logic_LF", "LF.AnalysisOL"]
      impts3 = mkImports ["Common.ExtSign"]
      impts4 = mkImports [l ++ "." ++ "Syntax"]
      
      -- lid
      lid = mkLid l
      
      -- language
      descriptionI = mkImpl "description" l "\"User-defined logic.\""
      lang = mkInst "Language" l [] [descriptionI]
     
      -- syntax
      parse_basic_specI = inheritImpl "parse_basic_spec" l ml
      parse_symb_itemsI = inheritImpl "parse_symb_items" l ml
      parse_symb_map_itemsI = inheritImpl "parse_symb_map_items" l ml
      
      syntax = mkInst "Syntax" l
                [basic_specC, symb_itemsC, symb_map_itemsC]
                [parse_basic_specI, parse_symb_itemsI, parse_symb_map_itemsI]
    
      -- sentences
      map_senI = inheritImpl "map_sen" l ml
      sym_ofI = inheritImpl "sym_of" l ml

      sentences = mkInst "Sentences" l [sentenceC, signC, morphismC,
                    symbolC] [map_senI, sym_ofI]
     
      -- logic
      logic = mkInst "Logic" l [sublogicsC, basic_specC, sentenceC,
                symb_itemsC, symb_map_itemsC, signC, morphismC,
                symbolC, raw_symbolC, proof_treeC] []

      -- static analysis
      basic_analysisI = mkImpl "basic_analysis" l
         " Just $ basicAnalysisOL ltruth"
      stat_symb_itemsI = inheritImpl "stat_symb_items" l ml
      stat_symb_map_itemsI = inheritImpl "stat_symb_map_items" l ml
      symbol_to_rawI = inheritImpl "symbol_to_raw" l ml
      matchesI = inheritImpl "matches" l ml
      empty_signatureI = mkImpl "empty_signature" l " cod $ ltruth"
      is_subsigI = inheritImpl "is_subsig" l ml
      subsig_inclusionI = inheritImpl "subsig_inclusion" l ml
      signature_unionI = inheritImpl "signature_union" l ml
      induced_from_to_morphismI = mkFullImpl "induced_from_to_morphism"
         l ["m", "(ExtSign sig1 _)", "(ExtSign sig2 _)"] $ "\n      " ++
         "inducedFromToMorphism (translMapAnalysisOL ltruth m sig1 sig2) " ++
         "sig1 sig2"
      
      analysis = mkInst "StaticAnalysis" l
                   [basic_specC, sentenceC, symb_itemsC, symb_map_itemsC,
                    signC, morphismC, symbolC, raw_symbolC]
                   [basic_analysisI, stat_symb_itemsI, stat_symb_map_itemsI,
                    symbol_to_rawI, matchesI, empty_signatureI, is_subsigI,
                    subsig_inclusionI, signature_unionI,
                    induced_from_to_morphismI]

      -- file
      header = comp_opt
      body = intercalate "\n\n" $
               [mod_decl, impts1, impts2, impts3, impts4, lid, lang, syntax,
                sentences, logic, analysis] 
      in header ++ "\n" ++ body

-----------------------------------------------------------------
-----------------------------------------------------------------

writeSyntax :: String -> Morphism -> String
writeSyntax l ltruth =
  let -- module declaration
      mod_decl = mkModDecl $ l ++ "." ++ "Syntax"
      
      -- imports
      impts1 = mkImports ["LF.Sign", "LF.Morphism"]
      impts2 = mkImports ["Data.Map"]      
      
      -- ltruth declaration
      ltruth_decl = mkDecl "ltruth" "Morphism" $ show ltruth
 
      in intercalate "\n\n" [mod_decl, impts1, impts2, ltruth_decl]

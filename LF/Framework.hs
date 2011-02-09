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
baseB = "logics/propositional/syntax/base.elf"

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
      raw_symbolC = "Symbol"
      sublogicsC = "()"
      proof_treeC = "()"
      
      -- module declaration
      comp_opt = mkCompOpt [multiOpt,synOpt]
      mod_decl = mkModDecl $ l ++ "." ++ "Logic_" ++ l
      
      -- imports
      impts1 = mkImports ["Logic.Logic"]
      impts2 = mkImports ["LF.AS", "LF.Sign", "LF.Morphism",
                          "LF.Logic_LF", "LF.AnalysisOL"]
      impts3 = mkImports [l ++ "." ++ "Syntax"]
      
      -- lid
      lid = mkLid l
      
      -- language
      descriptionI = mkImpl "description" l "\"User-defined logic.\""
      lang = mkInst "Language" l [] [descriptionI]
     
      -- syntax
      parse_basic_specI = mkImpl "parse_basic_spec" l "parse_basic_spec LF"
      parse_symb_itemsI = mkImpl "parse_symb_items" l "parse_symb_items LF"
      parse_symb_map_itemsI = mkImpl "parse_symb_map_items" l
                                "parse_symb_map_items LF"
      
      syntax = mkInst "Syntax" l
                [basic_specC, symb_itemsC, symb_map_itemsC]
                [parse_basic_specI, parse_symb_itemsI, parse_symb_map_itemsI]
    
      -- sentences
      map_senI = mkImpl "map_sen" l "map_sen LF"
      sym_ofI = mkImpl "sym_of" l "sym_of LF"

      sentences = mkInst "Sentences" l [sentenceC, signC, morphismC,
                    symbolC] [map_senI, sym_ofI]
     
      -- logic
      logic = mkInst "Logic" l [sublogicsC, basic_specC, sentenceC,
                symb_itemsC, symb_map_itemsC, signC, morphismC,
                symbolC, raw_symbolC, proof_treeC] []

      -- static analysis
      basic_analysisI = mkImpl "basic_analysis" l
                          "Just $ basicAnalysisOL ltruth"
      empty_signatureI = mkImpl "empty_signature" l "cod $ ltruth"
      signature_unionI = mkImpl "signature_union" l "signature_union LF"
      is_subsigI = mkImpl "is_subsig" l "is_subsig LF"
      subsig_inclusionI = mkImpl "subsig_inclusion" l "subsig_inclusion LF"

      analysis = mkInst "StaticAnalysis" l
                   [basic_specC, sentenceC, symb_itemsC, symb_map_itemsC,
                    signC, morphismC, symbolC, raw_symbolC]
                   [basic_analysisI, empty_signatureI, signature_unionI,
                    is_subsigI, subsig_inclusionI]

      -- file
      header = comp_opt
      body = intercalate "\n\n" $
               [mod_decl, impts1, impts2, impts3, lid, lang, syntax, sentences,
                logic, analysis] 
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

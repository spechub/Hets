{- |
Module      :  $Header$
Description :  Utility functions for defining the Edinburgh Logical Framework
               as an instance of LogicFram
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Framework where

import LF.AS
import LF.Sign
import LF.Morphism
import LF.Analysis
import LF.Twelf2GR

import Framework.WriteLogic

import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Result

import Data.List

import System.IO.Unsafe

baseSigLF :: Sign
baseSigLF =
  let b = ""
      m = "Base"
      o = Symbol b m "o"
      ded = Symbol b m "ded"
      in Sign b m
         [ Def o Type Nothing
         , Def ded (Func [Const o] Type) Nothing ]

sen_type_symbol :: Symbol
sen_type_symbol = Symbol "" "Base" "o"

-----------------------------------------------------------------
-----------------------------------------------------------------

-- basic analysis for object logics of LF
basicAnalysisOL :: Morphism -> (BASIC_SPEC, Sign, GlobalAnnos) ->
                   Result (BASIC_SPEC, ExtSign Sign Symbol, [Named EXP])
basicAnalysisOL ltruth (bs@(Basic_spec items), initsig, _) =
  if initsig /= target ltruth
     then error "Structuring for LF nyi."
     else do
       let (sig,sen) = unsafePerformIO $
             constructSigSenOL ltruth gen_file gen_sig items
       let syms = getSymbols sig
       let fs = makeNamedForms sen $ map r_annos $ getSenItems items
       return (bs, ExtSign sig syms, fs)

-- constructs the signatures and sentences
constructSigSenOL :: Morphism -> BASE -> MODULE ->
                     [Annoted BASIC_ITEM] -> IO (Sign,[(NAME,Sentence)])
constructSigSenOL ltruth fp name items = do
  file <- resolveToCur fp
  makeTwelfFileOL ltruth file name (getSigItems items) (getSenItems items)
  retrieveSigSen file name

-- constructs a Twelf file to analyze the signature and sentences
makeTwelfFileOL :: Morphism -> BASE -> MODULE ->
                 [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM] -> IO ()
makeTwelfFileOL ltruth file name sig_items sen_items = do
  let lsyn = target ltruth
  let sen_type = case mapSymbol sen_type_symbol ltruth of
                   Nothing -> error "Sentence type cannot be constructed."
                   Just t -> show $ pretty t
  let sig1 = wrapInSig (sigModule lsyn) $ show (pretty lsyn) ++ "\n"
  let sig2 = wrapInSig name $ wrapInIncl (sigModule lsyn) ++
               printSigItems sig_items
  let sig3 = wrapInSig (senSuf name) $ wrapInIncl name ++
               printSenItems sen_type sen_items
  writeFile file $ sig1 ++ "\n" ++ sig2 ++ "\n" ++ sig3

-----------------------------------------------------------------
-----------------------------------------------------------------

writeLogicLF :: String -> String
writeLogicLF l =
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
      impts2 = mkImports ["LF.AS", "LF.Parse", "LF.Sign", "LF.Morphism",
                          "LF.Framework", "LF.Logic_LF ()"]
      impts3 = mkImports [l ++ "." ++ "Syntax"]
      
      -- lid
      lid = mkLid l
      
      -- language
      descriptionI = mkImpl "description" l "\"User-defined logic.\""
      lang = mkInst "Language" l [] [descriptionI]
     
      -- syntax
      parse_basic_specI = mkImpl "parse_basic_spec" l "Just basicSpec"
      parse_symb_itemsI = mkImpl "parse_symb_items" l "Just symbItems"
      parse_symb_map_itemsI = mkImpl "parse_symb_map_items" l
                                "Just symbMapItems"
      
      syntax = mkInst "Syntax" l
                [basic_specC, symb_itemsC, symb_map_itemsC]
                [parse_basic_specI, parse_symb_itemsI, parse_symb_map_itemsI]
    
      -- sentences
      sentences = mkInst "Sentences" l [sentenceC, signC, morphismC,
                    symbolC] []
     
      -- logic
      logic = mkInst "Logic" l [sublogicsC, basic_specC, sentenceC,
                symb_itemsC, symb_map_itemsC, signC, morphismC,
                symbolC, raw_symbolC, proof_treeC] []

      -- static analysis
      empty_signatureI = mkImpl "empty_signature" l "cod $ ltruth"
      basic_analysisI = mkImpl "basic_analysis" l
                          "Just $ basicAnalysisOL ltruth"
      
      analysis = mkInst "StaticAnalysis" l
                   [basic_specC, sentenceC, symb_itemsC, symb_map_itemsC,
                    signC, morphismC, symbolC, raw_symbolC]
                   [empty_signatureI, basic_analysisI]

      -- file
      header = comp_opt
      body = intercalate "\n\n" $
               [mod_decl, impts1, impts2, impts3, lid, lang, syntax, sentences,
                logic, analysis] 
      in header ++ "\n" ++ body

-----------------------------------------------------------------
-----------------------------------------------------------------

writeSyntaxLF :: String -> Morphism -> String
writeSyntaxLF l ltruth =
  let -- module declaration
      mod_decl = mkModDecl $ l ++ "." ++ "Syntax"
      
      -- imports
      impts1 = mkImports ["LF.Sign", "LF.Morphism"]
      impts2 = mkImports ["Data.Map"]      
      
      -- ltruth declaration
      ltruth_decl = mkDecl "ltruth" "Morphism" $ show ltruth
 
      in intercalate "\n\n" [mod_decl, impts1, impts2, ltruth_decl]

{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Utility functions for defining the Edinburgh Logical Framework
               as an instance of LogicFram
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Framework where

import LF.AS
import LF.Sign
import LF.Morphism
import LF.Twelf2DG
import LF.Logic_LF

import Logic.Logic

import Framework.WriteLogic

import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Result

import Data.List
import qualified Data.Map as Map

import Static.DevGraph

import System.FilePath
import System.IO.Unsafe

instance LogicFram LF
   ()
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   ()
   where
   getBaseSig LF = baseSigLF
   writeLogic LF = writeLogicLF
   writeSyntax LF = writeSyntaxLF

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

----------------------------------------------------
----------------------------------------------------

gen_file :: String
gen_file = "Framework/test/gen_twelf_file.elf"

gen_sig :: String
gen_sig = "GEN_SIG"

gen_ax :: String
gen_ax = "gen_ax"

senSuf :: String -> String
senSuf sn = sn ++ "_SEN"

numSuf :: String -> Int -> String
numSuf s i = s ++ "_" ++ show i

wrapInSig :: String -> String -> String
wrapInSig sn cont = "%sig " ++ sn ++ " = {\n" ++ cont ++ "}.\n"

wrapInIncl :: String -> String
wrapInIncl sn = "%include " ++ sn ++ " %open.\n"

getSigItems :: [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM]
getSigItems = filter ( \ (Annoted i _ _ _) ->
  case i of
    Decl _ -> True
    Form _ -> False )

getSenItems :: [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM]
getSenItems = filter ( \ (Annoted i _ _ _) ->
  case i of
    Decl _ -> False
    Form _ -> True )

getSensFromDefs :: [DEF] -> [(NAME,Sentence)]
getSensFromDefs [] = []
getSensFromDefs ((Def s _ (Just v)):ds) = (symName s, v) : getSensFromDefs ds
getSensFromDefs _ = error "Sentences cannot be retrieved from definitions."

makeNamedForms :: [(NAME,Sentence)] -> [[Annotation]] -> [Named Sentence]
makeNamedForms ss as = map makeNamedForm $ zip ss as

makeNamedForm :: ((NAME,Sentence),[Annotation]) -> Named Sentence
makeNamedForm ((n,s),annos) =
  let implies = or $ map isImplies annos
      implied = or $ map isImplied annos
      isTheorem = implies || implied
      in (makeNamed n s) {isAxiom = not isTheorem}

-----------------------------------------------------------------
-----------------------------------------------------------------

-- basic analysis for object logics of LF
basicAnalysis :: Morphism -> (BASIC_SPEC, Sign, GlobalAnnos) ->
                 Result (BASIC_SPEC, ExtSign Sign Symbol, [Named EXP])
basicAnalysis ltruth (bs@(Basic_spec items), initsig, _) =
  if initsig /= target ltruth
     then error "Structuring for LF nyi."
     else do
       let (sig,sen) = unsafePerformIO $
             constructSigSen ltruth gen_file gen_sig items
       let syms = getSymbols sig
       let fs = makeNamedForms sen $ map r_annos $ getSenItems items
       return (bs, ExtSign sig syms, fs)

-- constructs the signatures and sentences
constructSigSen :: Morphism -> BASE -> MODULE ->
                   [Annoted BASIC_ITEM] -> IO (Sign,[(NAME,Sentence)])
constructSigSen ltruth fp name items = do
  file <- resolveToCur fp
  makeTwelfFile ltruth file name (getSigItems items) (getSenItems items)
  retrieveSigSen file name

-- constructs a Twelf file to analyze the signature and sentences
makeTwelfFile :: Morphism -> BASE -> MODULE ->
                 [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM] -> IO ()
makeTwelfFile ltruth file name sig_items sen_items = do 
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

printSigItems :: [Annoted BASIC_ITEM] -> String
printSigItems [] = ""
printSigItems (i:is) =
  case i of
    Annoted (Decl d) _ _ _ -> d ++ ".\n" ++ printSigItems is
    _ -> printSigItems is

printSenItems :: String -> [Annoted BASIC_ITEM] -> String
printSenItems sen_type items = printSenItemsH sen_type 0 items

printSenItemsH :: String -> Int -> [Annoted BASIC_ITEM] -> String
printSenItemsH _ _ [] = ""
printSenItemsH sen_type num (i:is) =
  case i of
    Annoted (Form f) _ _ _ ->
      let lab  = getRLabel i
          lab' = if null lab then numSuf gen_ax num else lab
          num' = if null lab then num + 1 else num
          in lab' ++ " : " ++ sen_type ++ " = " ++ f ++ ".\n" ++
             printSenItemsH sen_type num' is
    _ -> printSenItemsH sen_type num is

{- retrieves the signature and sentences corresponding to the
   original basic spec out of a Twelf file -}
retrieveSigSen :: BASE -> MODULE -> IO (Sign,[(NAME,Sentence)])
retrieveSigSen file name = do
  runTwelf file
  (_,_,(sigmap,_)) <- buildGraph file (emptyLibEnv,emptyGrMap)

  let base = dropExtension file
  let name' = senSuf name
  let sig = Map.findWithDefault (error $ name ++ " not found.")
               (base,name) sigmap
  let sig' = Map.findWithDefault (error $ name' ++ " not found.")
               (base,name') sigmap

  let sens = getSensFromDefs $ filter (\ d -> isLocalSym (getSym d) sig')
               $ getDefs sig'
  return (sig,sens)

----------------------------------------------------
----------------------------------------------------

writeLogicLF :: String -> String
writeLogicLF l =
  let -- module declaration
      comp_opt = mkCompOpt [multiOpt,synOpt]
      mod_decl = mkModDecl $ l ++ "." ++ "Logic_" ++ l
      
      -- imports
      impts1 = mkImports ["Logic.Logic"]
      impts2 = mkImports ["LF.AS", "LF.Parse", "LF.Sign", "LF.Morphism",
                          "LF.Framework"]
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
                ["BASIC_SPEC", "SYMB_ITEMS", "SYMB_MAP_ITEMS"]
                [parse_basic_specI, parse_symb_itemsI, parse_symb_map_itemsI]
    
      -- sentences
      sentences = mkInst "Sentences" l ["Sentence", "Sign", "Morphism",
                    "Symbol"] []
     
      -- logic
      logic = mkInst "Logic" l ["()", "BASIC_SPEC", "Sentence",
                "SYMB_ITEMS", "SYMB_MAP_ITEMS", "Sign", "Morphism",
                "Symbol", "Symbol", "()"] []

      -- static analysis
      empty_signatureI = mkImpl "empty_signature" l "cod $ ltruth"
      basic_analysisI = mkImpl "basic_analysis" l "Just $ basicAnalysis ltruth"
      
      analysis = mkInst "StaticAnalysis" l
                   ["BASIC_SPEC", "Sentence", "SYMB_ITEMS", "SYMB_MAP_ITEMS",
                    "Sign", "Morphism", "Symbol", "Symbol"]
                   [empty_signatureI, basic_analysisI]

      -- file
      header = comp_opt
      body = intercalate "\n\n" $
               [mod_decl, impts1, impts2, impts3, lid, lang, syntax, sentences,
                logic, analysis] 
      in header ++ "\n" ++ body

----------------------------------------------------
----------------------------------------------------

writeSyntaxLF :: String -> Morphism -> String
writeSyntaxLF l ltruth =
  let -- module declaration
      mod_decl = mkModDecl $ l ++ "." ++ "Syntax"
      
      -- imports
      impts = mkImports ["LF.Sign", "LF.Morphism"]
      
      -- ltruth declaration
      ltruth_decl = mkDecl "ltruth" "Morphism" $ show ltruth
 
      in intercalate "\n\n" [mod_decl, impts, ltruth_decl]

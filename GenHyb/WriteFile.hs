{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/WriteFile
Description :  writes the new instance of hybrid logic


-}

module GenHyb.WriteFile where

import qualified Data.Map as Map

import Logic.SemConstr
import Logic.HDef
import Logic.Logic

import Logic.Grothendieck
import Logic.ExtSign

import qualified GenHyb.GenTypes as GTypes
import qualified GenHyb.GenMethods as GMethods
import qualified GenHyb.Logic_Hyb as GLogic

import System.Directory

import Static.DevGraph
import Static.DgUtils
import Static.GTheory

import Common.IRI
import Common.Id
import Common.Result

import qualified Framework.Analysis as FAna
import Framework.WriteLogicUtils

import Data.List
import Syntax.AS_Structured

anaHLogicDef :: HLogicDef -> DGraph -> LogicGraph -> IO DGraph
anaHLogicDef hld dg lg = do 
  buildLogicInstance hld lg
  FAna.addLogic2LogicList $ newHybridLogicName hld
  let dg' = addHLogicDef2DG hld dg
  return dg'

-- creates a node for the logic definition
addHLogicDef2DG :: HLogicDef -> DGraph -> DGraph
addHLogicDef2DG hld dg =
  let node = getNewNodeDG dg
      name = newHybridLogicName hld
      nodeName = emptyNodeName { getName = mkIRI name }
      info = newNodeInfo DGBasic
      extSign = makeExtSign GLogic.Hyb hld
      gth = noSensGTheory GLogic.Hyb extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node, nodeLabel) dg

      emptyNode = EmptyNode $ Logic GLogic.Hyb
      genSig = GenSig emptyNode [] emptyNode
      nodeSig = NodeSig node $ G_sign GLogic.Hyb extSign startSigId
      gEntry = SpecEntry $ ExtGenSig genSig nodeSig
      dg2 = dg1 { globalEnv = Map.insert (mkIRI name) gEntry $ globalEnv dg1 }
   in dg2

buildLogicInstance :: HLogicDef -> LogicGraph -> IO ()
buildLogicInstance hld lg = do
 let l = newHybridLogicName hld
 exists <- doesDirectoryExist l
 if exists then
     error $ "The directory " ++ l ++ " already exists.\n" ++
             "Please choose a different object logic name." else do
     createDirectory l
     let logicInst = writeLogic hld lg
     writeFile (l ++ "/" ++ "Logic_" ++ l ++ ".hs") logicInst
     return ()

writeLogic :: HLogicDef -> LogicGraph -> String
writeLogic hld lg = let
  -- logic constituents
   l = newHybridLogicName hld
   (logic, _msubl) = baseLogicName hld
   Result ds maybeLid = lookupLogic "GenHyb.writeLogic" logic lg
   hasQNominals = (mkSimpleId "nominal", Nothing) `elem` (varKinds hld)
   kVars = map show $ filter (\x -> not (x == mkSimpleId "nominal")) $ map fst $ varKinds hld
   constrs = show $ semConstrs hld
 in case maybeLid of 
      Nothing -> error $ "logic not found:" ++ show ds
      Just (Logic baseLid) -> let
      -- module declaration
        header = mkCompOpt [multiOpt, synOpt, flexOpt]
        mod_decl = mkModDecl $ l ++ "." ++ "Logic_" ++ l

        gimports = ["import Logic.Logic",
                    "import Logic.SemConstr",
                    "import qualified Data.Map as Map",
                    "import qualified GenHyb.GenTypes as GTypes",
                    "import qualified GenHyb.GenMethods as GMethods"] ++
                   ["import " ++ logic ++ "." ++ "Logic_" ++ logic]

        (_sublType, sublPath) = sublogicsTypeName baseLid
        (_basicSpecType, basicSpecPath) = basicSpecTypeName baseLid
        (senType, senPath) = sentenceTypeName baseLid
        (siType, siPath) = symbItemsTypeName baseLid
        (_smiType, smiPath) = symbMapItemsTypeName baseLid
        (signType, signPath) = signTypeName baseLid
        (morType, morPath) = morphismTypeName baseLid
        (symType, symPath) = symbolTypeName baseLid
        (rsymType, rsymPath) = rawSymbolTypeName baseLid
        (_ptType, ptPath) = proofTreeTypeName baseLid
        import1 = let importFiles = nub $ [sublPath, basicSpecPath, 
                                     senPath, siPath, smiPath, signPath, morPath, 
                                     symPath, rsymPath, ptPath]
                  in if null importFiles then error "empty imports, helpers for base logic not set"
                      else mkImports importFiles

        inBracks s = "(" ++ s ++ ")" 

        hSublType = "()"
         -- H_BASIC_SPEC sen symb_items raw_sym
        hBasicSpecType = inBracks $ "GTypes.H_BASIC_SPEC " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- HFORMULA sen symb_items raw_sym
        hSenType = inBracks $ "GTypes.HFORMULA " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- H_SYMB_ITEMS sym symb_items
        hSiType = inBracks $ "GTypes.H_SYMB_ITEMS " ++ symType ++ " " ++ siType
        hSmiType = "()" -- for now!
         -- HSign sig
        hSignType = inBracks $ "GTypes.HSign " ++ signType
         -- HMorphism sig mor
        hMorType = inBracks $ "GTypes.HMorphism " ++ signType ++ " " ++ morType
         -- HSymbol sym
        hSymType = inBracks $  "GTypes.HSymbol " ++ symType
         -- HRawSymbol sym raw_sym
        hRSymType = inBracks $ "GTypes.HRawSymbol " ++ symType ++ " " ++ rsymType
        hPtType = "()"

        -- lid
        newLid = mkLid l

        -- language
        descriptionI = mkImpl "description" l "\"User-defined hybrid logic.\""
        lang = mkInst "Language" l [] [descriptionI]

        -- category

        genDom = mkImpl "dom" "" "GTypes.source"
        genCod = mkImpl "cod" "" "GTypes.target"
        genIde = mkImpl "ide" "" "GMethods.idMor"
        genIsIncl = mkImpl "isInclusion" "" "GMethods.isHIncl"
        genCompMor = mkImpl "composeMorphisms" "" "GMethods.compHMor"

        category = mkInst "Category" "" [hSignType, hMorType]
                     [genDom, genCod, genIde, genIsIncl, genCompMor]

        -- syntax

        genParseBasicSpec = mkImpl "parse_basic_spec" l $
                             "Just $ GMethods.parseHBasicSpec " ++ 
                              if hasQNominals then "True " else "False " ++
                              (show $ not $ null kVars) ++ " " ++ logic
        genParseSymbItems = mkImpl "parse_symb_items" l
                              "error \"nyi\" "
        genParseSymbMapItems = mkImpl "parse_symb_map_items" l 
                              "error \"nyi\" "

        syntax = mkInst "Syntax" l
                [hBasicSpecType, hSymType, hSiType, hSmiType]
                [genParseBasicSpec, genParseSymbItems, genParseSymbMapItems]

        -- sentences

        genMapSen = mkImpl "map_sen" l $
                     "GMethods.mapSentence " ++ logic
  
        genNegation = mkImpl "negation" l "GMethods.hNegation"
 
        genSymOf = mkImpl "sym_of" l $ "GMethods.hSymOf " ++ logic

        genSymName = mkImpl "sym_name" l $ "GMethods.hSymName " ++ logic
  
        genSymKind = mkImpl "symKind" l $ "GMethods.symKindH " ++ logic
  
        genSymsOfSen = mkImpl "symsOfSen" l $ "GMethods.symsOfHSen " ++ logic 
     
        genMostSymsOf = mkImpl "mostSymsOf" l $           
                         "GMethods.mostSymsOfDiff " ++ logic 

        
        sentences = mkInst "Sentences" l 
                     [hSenType, hSignType, hMorType, hSymType]  
                     [genMapSen, genNegation, genSymOf, genSymName, 
                      genSymKind, genSymsOfSen, genMostSymsOf]

        -- static
        genBasicAnalysis = 
                  mkImpl "basic_analysis" l $ -- TODO: check that args are right!
                   "Just $ GMethods.basicHAnalysis " ++ 
                   if hasQNominals then "True " else "False " ++
                   (show kVars) ++ " " ++ logic
  
        genSenAnalysis = 
              mkImpl "sen_analysis" l $ "Nothing" -- TODO: for now
               {- "Just $ GMethods.anaHFORMULA " ++ 
                   if hasQNominals then "True " else "False " ++
                   (show kVars) ++ " " ++ logic -}

        genSigColimit = mkImpl "signature_colimit" l $ 
                          "GMethods.signatureColimit " ++ logic

        genSymbolToRaw = mkImpl "symbol_to_raw" l "GTypes.ASymbol"

        genRawToSymbol = mkImpl "raw_to_symbol" l $ 
                          "GMethods.rawToSymbol " ++ logic
  
        genIdToRaw = mkImpl "id_to_raw" l $
                          "GMethods.idToRaw " ++ logic 

        genEmptySig = mkImpl "empty_signature" l $
                          "GMethods.emptyHSign " ++ logic 

        genAddSymbToSign = mkImpl "add_symb_to_sign" l $ 
                            "GMethods.addSymbToHSign " ++ logic

        genSigDiff = mkImpl "signatureDiff" l $ 
                         "GMethods.signatureDifference " ++ logic
 
        genSubsigIncl = mkImpl "subsig_inclusion" l $ 
                         "GMethods.subsigInclusion " ++ logic
     
        genSigUnion = mkImpl "signature_union" l $ 
                         "GMethods.sigUnion " ++ logic

        static = mkInst "StaticAnalysis" l
                  [hBasicSpecType, hSenType, hSiType, hSmiType,
                   hSignType, hMorType, hSymType, hRSymType] 
                  [genBasicAnalysis, genSenAnalysis, genSigColimit,
                   genSymbolToRaw, genRawToSymbol, genIdToRaw,
                   genEmptySig, genAddSymbToSign, genSigUnion, genSigDiff,
                   genSubsigIncl] -- TODO: add methods here as you implement them in GMethods


        -- logic

        genSemConstr = mkImpl "sem_constr" l
                        constrs

        logicInst = mkInst "Logic" l 
                     [hSublType, hBasicSpecType, hSenType, 
                      hSiType, hSmiType, hSignType, hMorType,
                      hSymType, hRSymType, hPtType] 
                     [genSemConstr]


        body = intercalate "\n\n" $ 
                [mod_decl] ++ gimports ++ [import1, newLid, lang, category, syntax, sentences, static, logicInst]

       in header ++ "\n" ++ body


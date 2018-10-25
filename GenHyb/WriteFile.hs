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
import Logic.Comorphism

import Logic.Grothendieck
import Logic.ExtSign

import qualified GenHyb.GenTypes as GTypes
import qualified GenHyb.GenMethods as GMethods
import qualified GenHyb.Logic_Hyb as GLogic

import GenHyb.GenInsts

import GenHyb.GenComor

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
import Debug.Trace
-- import Syntax.AS_Structured

import qualified CASL.Logic_CASL as CLogic

-- comorphism definition

anaHComDef :: HComDef -> DGraph -> LogicGraph -> IO DGraph
anaHComDef hcd dg lg = do
 let com = newHComName hcd
     hLogic = sourceHLogic hcd
     bcom = baseComName hcd
     Result ds mcom = lookupComorphism bcom lg
 case mcom of 
  Nothing -> error $ "could not find base comorphism:" ++ show bcom ++ "\nOriginal error:" ++ show ds
  Just bc -> do
   let Result ds' maybeLid = lookupLogic "GenHyb.anaHComDef" hLogic lg
   case maybeLid of
    Nothing -> error $ "could not find hybrid logic:" ++ show hLogic ++ "\nOriginal error:" ++ show ds'
    Just hlid -> do
     buildComorInstance lg bc hlid com
     FAna.addComorphism2ComorphismList $ com
     return dg

buildComorInstance :: LogicGraph -> AnyComorphism -> AnyLogic -> String -> IO ()
buildComorInstance lg bc hlid com = do
 writeFile ("Comorphisms/" ++ com ++ ".hs") $ comDef lg bc hlid com
 return ()

comDef :: LogicGraph -> AnyComorphism -> AnyLogic -> String -> String
comDef _lg (Comorphism baseCid) (Logic hLid) com = let 

  hLogic = show hLid
  bCom = show baseCid 
  header = mkCompOpt [multiOpt, synOpt, flexOpt]
  mod_decl = mkModDecl $ "Comorphisms." ++ com
  
  hLogicPath = hLogic ++".Logic_" ++ hLogic -- import this for the lid
  (hSublType, sublPath) = if sublogicsTypeName hLid == ("","") then ("()","") else sublogicsTypeName hLid
  (hBasicSpecType, basicSpecPath) = basicSpecTypeName hLid
  (hSenType, senPath) = sentenceTypeName hLid
  (hSiType, siPath) = symbItemsTypeName hLid
  (hSmiType, smiPath) = if symbMapItemsTypeName hLid == ("","") then ("()","") else symbMapItemsTypeName hLid
  (hSignType, signPath) = signTypeName hLid
  (hMorType, morPath) = morphismTypeName hLid
  (hSymType, symPath) = symbolTypeName hLid
  (hRSymType, rsymPath) = rawSymbolTypeName hLid
  (hPtType, ptPath) = if proofTreeTypeName hLid == ("","") then ("()","") else proofTreeTypeName hLid
  import1 = let importFiles = filter (\x -> not $ null x ) $ nub $ [hLogicPath, sublPath, basicSpecPath, 
                                      senPath, siPath, smiPath, signPath, morPath, 
                                      symPath, rsymPath, ptPath]
             in if null importFiles then error "empty imports, helpers for hybrid logic not set"
                      else mkImports importFiles

  (sublTypeCASL, sublPathCASL) = sublogicsTypeName CLogic.CASL
  (basicSpecTypeCASL, basicSpecPathCASL) = basicSpecTypeName CLogic.CASL
  (senTypeCASL, senPathCASL) = sentenceTypeName CLogic.CASL
  (siTypeCASL, siPathCASL) = symbItemsTypeName CLogic.CASL
  (smiTypeCASL, smiPathCASL) = symbMapItemsTypeName CLogic.CASL
  (signTypeCASL, signPathCASL) = signTypeName CLogic.CASL
  (morTypeCASL, morPathCASL) = morphismTypeName CLogic.CASL
  (symTypeCASL, symPathCASL) = symbolTypeName CLogic.CASL
  (rsymTypeCASL, rsymPathCASL) = rawSymbolTypeName CLogic.CASL
  (ptTypeCASL, ptPathCASL) = proofTreeTypeName CLogic.CASL
  import2 = let importFiles = filter (\x -> not $ null x ) $ nub $ [sublPathCASL, basicSpecPathCASL, 
                                      senPathCASL, siPathCASL, smiPathCASL, signPathCASL, morPathCASL, 
                                      symPathCASL, rsymPathCASL, ptPathCASL]
             in if null importFiles then error "empty imports, helpers for CASL logic not set" -- should never happen, they are set
                      else mkImports importFiles
  imports = ["import Logic.Logic", 
             "import Logic.Comorphism",
             "import qualified Data.Set as Set",
             "import qualified Data.Map as Map",
             "import Common.Result",
             "import Common.AS_Annotation",
             "import Common.Id",
             "import qualified GenHyb.GenTypes as GTypes", -- for methods only
             "import qualified GenHyb.GenComor as GComor"
                 ]

  cPath = mkImports[com_path baseCid]

  mkCid = mkLid com

  -- comorphism
 
  genSourceLogic = mkImpl "sourceLogic" com hLogic
 
  genTargetLogic = mkImpl "targetLogic" com "CASL"
  
  genSourceSublogic = mkImpl "sourceSublogic" com $ 
                             "top_sublogic " ++ hLogic

  genMapSublogic = mkImpl "mapSublogic" com "const $ Just cFol { cons_features = emptyMapConsFeature }"

       -- genInclCom = mkImpl "isInclusionComorphism" cid "True"

  genMapTheory = mkImpl "map_theory" com $ "GComor.mapTheoryConstr " ++ bCom ++ " " ++ hLogic

  genModelExpansion = mkImpl "has_model_expansion" com "True"

  -- genMapSen = mkImpl "map_sentence" (cid ++ " _ s") "return $ GTypes.Base_formula s nullRange"

  genLanguageName = mkImpl "language_name" com $ show com

  mkLangInst = mkInst "Language" com [] [genLanguageName]
  
  mkComInst = mkInst "Comorphism" com
                     [hLogic, hSublType, hBasicSpecType, hSenType, hSiType, hSmiType, hSignType, hMorType, hSymType, hRSymType, hPtType,
                      "CASL", sublTypeCASL, basicSpecTypeCASL, senTypeCASL, siTypeCASL, smiTypeCASL, signTypeCASL, morTypeCASL, symTypeCASL, rsymTypeCASL, ptTypeCASL] 
                     [genSourceLogic, genSourceSublogic, genTargetLogic, genMapSublogic, genMapTheory, genModelExpansion]

  body = intercalate "\n\n" $ 
                [mod_decl, import1, import2] ++ imports ++ [cPath, mkCid, mkLangInst, mkComInst] -- ++ genImports ++ [import1, mkCid, lang, mkComInst]
 in header ++ "\n" ++ body

-- logic definition

anaHLogicDef :: HLogicDef -> DGraph -> LogicGraph -> IO (DGraph, LogicGraph)
anaHLogicDef hld dg lg = do
  let l = newHybridLogicName hld
      (baseLogic, msubl) = baseLogicName hld
      hld' = if isExtension hld then
                let baseHld = Map.findWithDefault (error $ "Hybrid logic " ++ baseLogic ++ " not found") baseLogic $ knownHybLogics lg
                in hld {baseLogicName = baseLogicName baseHld,
                        semConstrs = semConstrs hld ++ semConstrs baseHld,
                        varKinds = varKinds hld ++ varKinds baseHld}
              else hld
      hlds = "HLogicDef \"" ++ l ++ "\" " ++ (show $ baseLogicName hld') ++ " " 
             ++ (show $ isExtension hld') ++ " "
             ++ (show $ semConstrs hld') ++ " " 
             ++ (show $ varKinds hld')
  trace ("hlds:" ++ hlds) $ buildLogicInstance hld' lg
  FAna.addLogic2LogicList l
  FAna.addHLogic $ "(\"" ++ l ++ "\", " ++ hlds ++ ")"
  let dg' = addHLogicDef2DG hld' dg
      lg' = lg {knownHybLogics = Map.insert l hld' $ knownHybLogics lg}
      (baseLogic', _) = baseLogicName hld' -- because if the new logic was declared as an extension, we want to add the comorphism from its base
  FAna.addComorphism2ComorphismList $ baseLogic' ++ "2" ++ l
  return (dg', lg')
  

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
     (baseLogic, _msubl) = baseLogicName hld
 exists <- doesDirectoryExist l
 if exists then
     error $ "The directory " ++ l ++ " already exists.\n" ++
             "Please choose a different object logic name." else do
     createDirectory l
     let typeDefs = writeTypes hld lg
         logicInst = writeLogic hld lg
         defaultImpDef = writeImplicitCom hld lg
     writeFile (l ++ "/" ++ "AS_" ++ l ++ ".hs") typeDefs
     writeFile ("Comorphisms/" ++ baseLogic ++ "2" ++ l ++ ".hs") defaultImpDef
     writeFile (l ++ "/" ++ "Logic_" ++ l ++ ".hs") logicInst
     return ()

writeImplicitCom :: HLogicDef -> LogicGraph -> String
writeImplicitCom hld lg = let
   l = newHybridLogicName hld
   (logic, _msubl) = baseLogicName hld
   Result ds maybeLid = lookupLogic "GenHyb.writeLogic:" logic lg
   cid = logic ++ "2" ++ l
 in case maybeLid of 
     Nothing -> error $ "logic not found:" ++ show ds
     Just (Logic baseLid) -> let
       header = mkCompOpt [multiOpt, synOpt, flexOpt]
       mod_decl = mkModDecl $ "Comorphisms." ++ cid
       (sublType, sublPath) = if sublogicsTypeName baseLid == ("","") then ("()","") else sublogicsTypeName baseLid
       (basicSpecType, basicSpecPath) = basicSpecTypeName baseLid
       (senType, senPath) = sentenceTypeName baseLid
       (siType, siPath) = symbItemsTypeName baseLid
       (smiType, smiPath) = if symbMapItemsTypeName baseLid == ("","") then ("()","") else symbMapItemsTypeName baseLid
       (signType, signPath) = signTypeName baseLid
       (morType, morPath) = morphismTypeName baseLid
       (symType, symPath) = symbolTypeName baseLid
       (rsymType, rsymPath) = rawSymbolTypeName baseLid
       (ptType, ptPath) = if proofTreeTypeName baseLid == ("","") then ("()","") else proofTreeTypeName baseLid
       import1 = let importFiles = filter (\x -> not $ null x) $ nub $ [sublPath, basicSpecPath, 
                                     senPath, siPath, smiPath, signPath, morPath, 
                                     symPath, rsymPath, ptPath]
                  in if null importFiles then error "empty imports, helpers for base logic not set"
                      else mkImports importFiles
       hSublType = "()"
       hBasicSpecType = l ++ "_BASIC_SPEC"
       hSenType = l ++ "_FORMULA"
       hSiType = l ++ "_SYMB_ITEMS"
       hSmiType = "()" -- for now!
       hSignType = l ++ "_Sign"
       hMorType = l ++ "_Morphism"
       hSymType = l ++ "_Symbol"
       hRSymType = l ++ "_RawSymbol"
       hPtType = "()"
       imports = ["import Logic.Logic", 
                  "import Logic.Comorphism",
                  "import qualified Data.Set as Set",
                  "import qualified Data.Map as Map",
                  "import Common.Result",
                  "import Common.AS_Annotation",
                  "import Common.Id",
                  "import qualified GenHyb.GenTypes as GTypes" -- for methods only
                 ]
       genImports = ["import " ++ l ++ "." ++ "Logic_" ++ l,
                     "import " ++ l ++ ".AS_" ++ l,
                     "import " ++ logic ++ "." ++ "Logic_" ++ logic]
       mkCid = mkLid cid
       lang = mkInst "Language" cid [] []

       -- comorphism
 
       genSourceLogic = mkImpl "sourceLogic" cid logic
 
       genTargetLogic = mkImpl "targetLogic" cid l
  
       genSourceSublogic = mkImpl "sourceSublogic" cid $ 
                             "top_sublogic " ++ logic

       genMapSublogic = mkImpl "mapSublogic" cid "const $ Just ()"

       genInclCom = mkImpl "isInclusionComorphism" cid "True"

       genMapTheory = mkImpl "map_theory" (cid ++ " (sig, nsens)") $
                       "do\n"++
                       "         let tsig = GTypes.HSign sig (Set.singleton $ genName \"i\") Map.empty\n" ++
                       "             tsens = map ( \\nsen -> nsen{sentence = GTypes.Base_formula (sentence nsen) nullRange} ) nsens\n" ++
                       "         return (tsig, tsens)" 

       genMapSen = mkImpl "map_sentence" (cid ++ " _ s") "return $ GTypes.Base_formula s nullRange"

  
       mkComInst = mkInst "Comorphism" cid
                     [logic, sublType, basicSpecType, senType, siType, smiType, signType, morType, symType, rsymType,ptType,
                      l, hSublType, hBasicSpecType, hSenType, hSiType, hSmiType, hSignType, hMorType, hSymType, hRSymType, hPtType] 
                     [genSourceLogic, genSourceSublogic, genTargetLogic, genMapSublogic, genMapTheory, genMapSen, genInclCom]

       body = intercalate "\n\n" $ 
                [mod_decl] ++ imports ++ genImports ++ [import1, mkCid, lang, mkComInst]
      in header ++ "\n" ++ body


writeTypes :: HLogicDef -> LogicGraph -> String
writeTypes hld lg = 
 let 
  l = newHybridLogicName hld
  (logic, _msubl) = baseLogicName hld
  Result ds maybeLid = lookupLogic "GenHyb.writeLogic:" logic lg
 in case maybeLid of 
     Nothing -> error $ show ds
     Just (Logic baseLid) -> 
      let
       header = mkCompOpt [multiOpt, synOpt, flexOpt]
       mod_decl = mkModDecl $ l ++ "." ++ "AS_" ++ l
       gimports = [ "import qualified Data.Map as Map",
                    "import qualified GenHyb.GenTypes as GTypes"
                    ] ++
                   ["import " ++ logic ++ "." ++ "Logic_" ++ logic]
       (_sublType, sublPath) = sublogicsTypeName baseLid
       (basicSpecType, basicSpecPath) = basicSpecTypeName baseLid
       (senType, senPath) = sentenceTypeName baseLid
       (siType, siPath) = symbItemsTypeName baseLid
       (smiType, smiPath) = symbMapItemsTypeName baseLid
       (signType, signPath) = signTypeName baseLid
       (morType, morPath) = morphismTypeName baseLid
       (symType, symPath) = symbolTypeName baseLid
       (rsymType, rsymPath) = rawSymbolTypeName baseLid
       (_ptType, ptPath) = proofTreeTypeName baseLid
       import1 = let importFiles = filter (\x -> not $ null x) $ nub $ [sublPath, basicSpecPath, 
                                     senPath, siPath, smiPath, signPath, morPath, 
                                     symPath, rsymPath, ptPath]
                  in if null importFiles then error "empty imports, helpers for base logic not set"
                      else mkImports importFiles
       -- drift = "--DrIFT command \n {-! global: GetRange !-}"
 
       hSublType = "()"
         -- H_BASIC_SPEC sen symb_items raw_sym
       hBasicSpecType = "type " ++ l ++ "_BASIC_SPEC = GTypes.H_BASIC_SPEC " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- HFORMULA sen symb_items raw_sym
       hSenType = "type " ++ l ++ "_FORMULA = GTypes.HFORMULA " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- H_SYMB_ITEMS sym symb_items
       hSiType = "type " ++ l ++ "_SYMB_ITEMS = GTypes.H_SYMB_ITEMS " ++ symType ++ " " ++ siType
         -- H_SYMB_MAP_ITEMS symb_map_items
       hSmiType = "type " ++ l ++ "_SYMB_MAP_ITEMS = GTypes.H_SYMB_MAP_ITEMS "  ++ smiType
         -- HSign sig
       hSignType = "type " ++ l ++ "_Sign = GTypes.HSign " ++ signType
         -- HMorphism sig mor
       hMorType = "type " ++ l ++ "_Morphism = GTypes.HMorphism " ++ signType ++ " " ++ morType
         -- HSymbol sym
       hSymType = "type " ++ l ++ "_Symbol = GTypes.HSymbol " ++ symType
         -- HRawSymbol sym raw_sym
       hRSymType = "type " ++ l ++ "_RawSymbol = GTypes.HRawSymbol " ++ symType ++ " " ++ rsymType
       hPtType = "()"
   
       body = intercalate "\n\n" $ 
                [mod_decl] ++ gimports ++ [import1, -- drift, 
                                           hBasicSpecType, hSenType, hSiType, hSmiType, hSignType, hMorType, hSymType, hRSymType]
      in header ++ "\n" ++ body

writeLogic :: HLogicDef -> LogicGraph -> String
writeLogic hld lg = let
  -- logic constituents
   l = newHybridLogicName hld
   (logic, msubl) = baseLogicName hld
   Result ds maybeLid = lookupLogic "GenHyb.writeLogic:" logic lg
   hasQNominals = ("nominal", Nothing) `elem` (varKinds hld)
   kVars = filter (\x -> not (x == "nominal")) $ map fst $ varKinds hld
   constrs = show $ semConstrs hld
 in case maybeLid of 
      Nothing -> error $ show ds
      Just (Logic baseLid) -> let
      -- module declaration
        header = mkCompOpt [multiOpt, synOpt, flexOpt]
        mod_decl = mkModDecl $ l ++ "." ++ "Logic_" ++ l

        gimports = ["import Logic.Logic",
                    "import Logic.SemConstr",
                    "import qualified Data.Map as Map",
                    "import qualified GenHyb.GenTypes as GTypes",
                    "import qualified GenHyb.GenMethods as GMethods",
                    "import GenHyb.GenInsts ()" ] ++
                   ["import " ++ logic ++ "." ++ "Logic_" ++ logic, 
                    "import " ++ l ++ ".AS_" ++ l ]

        (_sublType, sublPath) = sublogicsTypeName baseLid
        (_basicSpecType, basicSpecPath) = basicSpecTypeName baseLid
        (senType, senPath) = sentenceTypeName baseLid
        (siType, siPath) = symbItemsTypeName baseLid
        (smiType, smiPath) = symbMapItemsTypeName baseLid
        (signType, signPath) = signTypeName baseLid
        (morType, morPath) = morphismTypeName baseLid
        (symType, symPath) = symbolTypeName baseLid
        (rsymType, rsymPath) = rawSymbolTypeName baseLid
        (_ptType, ptPath) = proofTreeTypeName baseLid
        import1 = let importFiles = filter (\x -> not $ null x) $  nub $ [sublPath, basicSpecPath, 
                                     senPath, siPath, smiPath, signPath, morPath, 
                                     symPath, rsymPath, ptPath]
                  in if null importFiles then error "empty imports, helpers for base logic not set"
                      else mkImports importFiles

        -- inBracks s = "(" ++ s ++ ")" 

        hSublType = "()"
         -- H_BASIC_SPEC sen symb_items raw_sym
        hBasicSpecType = l ++ "_BASIC_SPEC"
         -- inBracks $ "GTypes.H_BASIC_SPEC " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- HFORMULA sen symb_items raw_sym
        hSenType = l ++ "_FORMULA" 
          -- inBracks $ "GTypes.HFORMULA " ++ senType ++ " " ++ siType ++ " " ++ rsymType
         -- H_SYMB_ITEMS sym symb_items
        hSiType = l ++ "_SYMB_ITEMS" 
          -- inBracks $ "GTypes.H_SYMB_ITEMS " ++ symType ++ " " ++ siType
        hSmiType = l ++ "_SYMB_MAP_ITEMS"
         -- HSign sig
        hSignType = l ++ "_Sign"
          -- inBracks $ "GTypes.HSign " ++ signType
         -- HMorphism sig mor
        hMorType = l ++ "_Morphism"
         -- inBracks $ "GTypes.HMorphism " ++ signType ++ " " ++ morType
         -- HSymbol sym
        hSymType = l ++ "_Symbol"
         -- inBracks $  "GTypes.HSymbol " ++ symType
         -- HRawSymbol sym raw_sym
        hRSymType = l ++ "_RawSymbol" 
         -- inBracks $ "GTypes.HRawSymbol " ++ symType ++ " " ++ rsymType
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
                             "Just $ GMethods.parseHBasicSpecEng " ++ 
                             (if hasQNominals then "True " else "False ") ++
                             (show $ not $ null kVars) ++ " " ++ logic

        genParseSymbItems = mkImpl "parse_symb_items" l $
                              "GMethods.parseSymbItems " ++ logic
 
        genParseSymbMapItems = mkImpl "parse_symb_map_items" l $ 
                              "GMethods.parseSymbMapItems " ++ logic

        genSymbItemsName = mkImpl "symb_items_name" l $
                              "GMethods.hSymbItemsName " ++ logic

        syntax = mkInst "Syntax" l
                [hBasicSpecType, hSymType, hSiType, hSmiType]
                [genParseBasicSpec, genParseSymbItems, genParseSymbMapItems,
                 genSymbItemsName]

        -- sentences

        genMapSen = mkImpl "map_sen" l $
                     "GMethods.mapSentence " ++ logic

        genSimplifySen = mkImpl "simplify_sen" l $ 
                     "GMethods.simplifyHSen " ++ logic
  
        genNegation = mkImpl "negation" l "GMethods.hNegation"
 
        genSymOf = mkImpl "sym_of" l $ "GMethods.hSymOf " ++ logic

        genSymName = mkImpl "sym_name" l $ "GMethods.hSymName " ++ logic
  
        genSymKind = mkImpl "symKind" l $ "GMethods.symKindH " ++ logic
  
        genSymsOfSen = mkImpl "symsOfSen" l $ "GMethods.symsOfHSen " ++ logic 
     
        genMostSymsOf = mkImpl "mostSymsOf" l $           
                         "GMethods.mostSymsOfDiff " ++ logic 

        
        sentences = mkInst "Sentences" l 
                     [hSenType, hSignType, hMorType, hSymType]  
                     [genMapSen, genSimplifySen, genNegation, genSymOf, genSymName, 
                      genSymKind, genSymsOfSen, genMostSymsOf]

        -- static
        genBasicAnalysis = 
                  mkImpl "basic_analysis" l $ -- TODO: check that args are right!
                   "Just $ GMethods.basicHAnalysis " ++ 
                   (if hasQNominals then "True " else "False ") ++
                   (show kVars) ++ " " ++ logic ++ 
                   (case msubl of 
                      Nothing -> " Nothing"
                      Just sName -> " (" ++ (show $ parseSublogic baseLid sName)  ++ ")"
                   ) 
  
        genSenAnalysis = 
              mkImpl "sen_analysis" l $ 
                  "GMethods.senAnalysis " ++ 
                  (if hasQNominals then "True " else "False ") ++
                   (show kVars) ++ " " ++ logic
 
        genStatSymbMapItems = mkImpl "stat_symb_map_items" l $ 
                           "GMethods.statSymbMapItems " ++ logic  
 
        genStatSymbItems = mkImpl "stat_symb_items" l $
                            "GMethods.hStatSymbItems " ++ logic

        genSigIntersection = mkImpl "intersection" l $
                             "GMethods.sigIntersection " ++ logic

        genSigColimit = mkImpl "signature_colimit" l $ 
                          "GMethods.signatureColimit " ++ logic

        genGeneratedSig = mkImpl "generated_sign" l 
                          $ "GMethods.hGeneratedSign " ++ logic

        genCoGeneratedSig = mkImpl "cogenerated_sign" l 
                          $ "GMethods.hCoGeneratedSign " ++ logic

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
       
        genIsSubsig = mkImpl "is_subsig" l $
                         "GMethods.isSubsig " ++ logic
 
        genSubsigIncl = mkImpl "subsig_inclusion" l $ 
                         "GMethods.subsigInclusion " ++ logic
     
        genSigUnion = mkImpl "signature_union" l $ 
                         "GMethods.sigUnion " ++ logic
        
        genInducedFromMorphism = mkImpl "induced_from_morphism" l $  
                          "GMethods.inducedFromMorphism " ++ logic

        genInducedFromToMorphism = mkImpl "induced_from_to_morphism" l $  
                          "GMethods.inducedFromToMorphism " ++ logic

        static = mkInst "StaticAnalysis" l
                  [hBasicSpecType, hSenType, hSiType, hSmiType,
                   hSignType, hMorType, hSymType, hRSymType] 
                  [genBasicAnalysis, genSenAnalysis, 
                   genStatSymbItems, genStatSymbMapItems, 
                   genSigIntersection, genSigColimit,
                   genGeneratedSig, genCoGeneratedSig,
                   genSymbolToRaw, genRawToSymbol, genIdToRaw,
                   genEmptySig, genAddSymbToSign, genSigUnion, genSigDiff,
                   genIsSubsig, genSubsigIncl,
                   genInducedFromMorphism, genInducedFromToMorphism]


        -- logic

        genSemConstr = mkImpl "sem_constr" l
                        constrs
     
        genConstrToSens = mkImpl "constr_to_sens" l $ "GMethods.constrToSens " ++ logic 
 
        genData = mkImpl "data_logic" l $ "Just $ Logic " ++ logic

        genParsePrimFormula = mkImpl "parse_prim_formula" l $  
                                "Just $ GMethods.hFormula " ++ 
                                (if hasQNominals then "True " else "False ") ++
                                (show $ not $ null kVars) ++ " " ++ logic --TODO: check that this fits with the modified version 

        typeDefFile = l ++ ".AS_" ++ l
  
        genBasicSpecType = mkImpl "basicSpecTypeName" l $ 
                              "(\"" ++ hBasicSpecType ++ "\", \"" ++ typeDefFile ++ "\")"

        --genSublType = mkImpl "sublogicsTypeName" l $ 
        --                      "(\"\", \"\")" -- default implementation is fine

        genSenType = mkImpl "sentenceTypeName" l $
                              "(\"" ++ hSenType ++ "\", \"" ++ typeDefFile ++ "\")"
        genSymbItemsType = mkImpl "symbItemsTypeName" l $ 
                              "(\"" ++ hSiType ++ "\", \"" ++ typeDefFile ++ "\")"
        
        genSignType = mkImpl "signTypeName" l $ 
                              "(\"" ++ hSignType ++ "\", \"" ++ typeDefFile ++ "\")" 
        genMorType = mkImpl "morphismTypeName" l $ 
                              "(\"" ++ hMorType ++ "\", \"" ++ typeDefFile ++ "\")"
        genSymType = mkImpl "symbolTypeName" l $ 
                              "(\"" ++ hSymType ++ "\", \"" ++ typeDefFile ++ "\")"
        genRSymType = mkImpl "rawSymbolTypeName" l $ 
                              "(\"" ++ hRSymType ++ "\", \"" ++ typeDefFile ++ "\")"

        genEmptyProofTree = mkImpl "empty_proof_tree" l "()"
        

        logicInst = mkInst "Logic" l 
                     [hSublType, hBasicSpecType, hSenType, 
                      hSiType, hSmiType, hSignType, hMorType,
                      hSymType, hRSymType, hPtType] 
                     [genSemConstr, genConstrToSens, genParsePrimFormula, genData, 
                      genEmptyProofTree,
                      genBasicSpecType, genSenType, genSymbItemsType, 
                      genSignType, genMorType, genSymType,genRSymType]


        body = intercalate "\n\n" $ 
                [mod_decl] ++ gimports ++ [import1, newLid, lang, category, syntax, sentences, static, logicInst]

       in header ++ "\n" ++ body


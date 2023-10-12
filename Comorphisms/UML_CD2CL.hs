{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Comorphisms.UML_CD2CL where

import Common.ProofTree
import Common.Result
import Common.Id
import Common.AS_Annotation

import Logic.Logic
import Logic.Comorphism

import UML.Sign
import UML.Logic_UML
import UML.UML hiding (Id)
import UML.UML2CL
import UML.UML2CL_preamble
import UML.Morphism

import CommonLogic.Sign as CL_Sign
import CommonLogic.Logic_CommonLogic
import CommonLogic.AS_CommonLogic as As_CL
import CommonLogic.Symbol as Symbol
import CommonLogic.ATC_CommonLogic ()
import CommonLogic.Sublogic
import CommonLogic.Morphism
import CommonLogic.Analysis

import qualified Data.Map as Map 
import qualified Data.Set as Set
-- | lid of the morphism
data UML_CD2CL = UML_CD2CL deriving Show

instance Language UML_CD2CL where
  language_name UML_CD2CL = "UML2CommonLogic" 

instance Comorphism UML_CD2CL 
    UML.Logic_UML.UML
    ()                    -- Sublogics
      UML.UML.CM                 -- basic_spec
    UML.Sign.Sen             -- sentence
      ()                    -- symb_items
      ()                    -- symb_map_items
      UML.Sign.Sign              -- sign
      UML.Morphism.Morphism                  -- morphism
      ()                    -- symbol
      ()                    -- raw_symbol
      ()                    -- proof_tree
    CommonLogic.Logic_CommonLogic.CommonLogic
    CommonLogicSL     -- Sublogics
    BASIC_SPEC        -- basic_spec
    TEXT_META         -- sentence
    SYMB_ITEMS        -- symb_items
    SYMB_MAP_ITEMS    -- symb_map_items
    CL_Sign.Sign              -- sign
    CommonLogic.Morphism.Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ProofTree         -- proof_tree
    where
        sourceLogic UML_CD2CL = UML.Logic_UML.UML
        targetLogic UML_CD2CL = CommonLogic.Logic_CommonLogic.CommonLogic
        map_theory UML_CD2CL = mapTheory
        map_morphism UML_CD2CL = mapMor 

mapTheory :: (UML.Sign.Sign, [Named Sen]) -> Result (CL_Sign.Sign, [Named TEXT_META])
mapTheory (sign, sens) = let 
                            sg = (mapSign sign)
                            t =  (translateSign2Phrases sign)   
                            tmSyms = (Set.fromList $ map symName $ foldl (++) [] $ map (symsOfTextMeta.sentence) tms) Set.\\ (allItems sg)
                            sg2 = CL_Sign.Sign{ discourseNames = Set.union (discourseNames sg) tmSyms,
                                                CL_Sign.nondiscourseNames = CL_Sign.nondiscourseNames sg,   
                                                sequenceMarkers = sequenceMarkers sg}
                            tms = (map (makeNamedSen.emptyAnno) t) ++   (map (mapNamed $ mapSen) sens)                   
                            in return (sg2 , tms)


mapSen ::  UML.Sign.Sen -> TEXT_META
mapSen mf = Text_meta{ As_CL.getText = Text phrases nullRange
                          , As_CL.textIri = Nothing
                          , As_CL.nondiscourseNames = Nothing
                          , As_CL.prefix_map = [] }
                    where phrases = (Sentence (translateMult2Sen mf)):[]--(translateSign2Phrases sign) 


mapSign :: UML.Sign.Sign -> CL_Sign.Sign 
mapSign sign = CL_Sign.Sign{
    CL_Sign.discourseNames =  Set.union (Set.fromList ((map (stringToId.showClassEntityName) $ fst $ signClassHier sign) 
                    ++ (map (stringToId.literalName) $ foldl (++) [] (map enumLiterals $ filterEnums $ fst $ signClassHier sign))
                    ++ (map morphTranslateAttr (signAttribute sign))
                    ++ (foldl (++) [] $ map morphTranslateOper (signOperations sign))
                    ++ (map morphTranslateComp (signCompositions sign))
                    ++ (foldl (++) [] $ map morphTranslateAsso (signAssociations sign))))  (foldl (Set.union) Set.empty preambleDiscourseNames),
    CL_Sign.nondiscourseNames = (foldl (Set.union) Set.empty preambleNonDiscourseNames),
    CL_Sign.sequenceMarkers = (foldl (Set.union) Set.empty preambleSequenceMarkers)
}

morphTranslateAttr :: (Class,String,Type) -> Id
morphTranslateAttr (c,s,_) = (stringToId $ className c ++ "." ++ s)

morphTranslateComp :: ((String,ClassEntity),String,(String,Type)) -> Id
morphTranslateComp ((_,_),n,(_,_)) = stringToId n

morphTranslateAsso :: (String,[(String,Type)]) -> [Id]
morphTranslateAsso (n,endL) = (stringToId n):(map (stringToId.fst) endL)

morphTranslateOper :: (Class,String,[(String,Type)],Type) -> [Id]
morphTranslateOper (c,n,para,_) = (stringToId $ (className c) ++ "." ++ n):(map (stringToId.fst) para)

mapMor :: UML.Morphism.Morphism -> Result CommonLogic.Morphism.Morphism 
mapMor m = return CommonLogic.Morphism.Morphism
  { CommonLogic.Morphism.source = mapSign $ UML.Morphism.source m
  , CommonLogic.Morphism.target = mapSign $ UML.Morphism.target m
  , CommonLogic.Morphism.propMap = Map.empty
  }

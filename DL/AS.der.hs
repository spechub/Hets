{- |
Module      :  $Header$
Description :  abstract syntax for DL logic similar to Manchester DL
Copyright   :  Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for DL logic 
-}

module DL.AS (DLConcept(..),
				DLRel,
				DLClassProperty(..),
				DLBasicItem(..),
				DLFacts(..),
				DLType(..),
				DLChars(..),
				DLIndRel(..),
				DLPropsRel(..),
				ISOLangCode,
				DLPara(..),
				DLBasic(..),
				map_sentence)
			where

-- | CASL-DL Abstract Syntax
-- | based on  the proposition of Manchester OWL Syntax

import Common.Id
import Common.AS_Annotation()
import Common.Doc
import Common.DocUtils
import DL.Sign
import Common.Result as Result
import qualified Data.Map as Map

-- DrIFT command
{-! global: UpPos !-}

data DLConcept = DLClassId Id | 
               DLAnd DLConcept DLConcept |
               DLOr DLConcept DLConcept |
               DLNot DLConcept |
               DLOneOf [Id] |
               DLSome DLRel DLConcept | 
               DLHas DLRel DLConcept | 
               DLOnly DLRel DLConcept |
               DLMin DLRel Int |
               DLMax DLRel Int |
               DLExactly DLRel Int |
               DLValue DLRel Id |
               DLThat DLConcept DLConcept |
               DLOnlysome DLRel [DLConcept] |
               DLXor DLConcept DLConcept
               deriving (Ord, Eq)

map_concept :: DLMorphism -> DLConcept -> Result.Result DLConcept
map_concept mor con = case con of
	DLClassId cid -> 
		do
			rpl <- Map.lookup cid $ c_map mor
			return $ DLClassId rpl
	DLAnd c1 c2 -> 
		do 
			tc1 <- map_concept mor c1
			tc2 <- map_concept mor c2
			return $ DLAnd tc1 tc2
	DLOr c1 c2 -> 
		do 
			tc1 <- map_concept mor c1
			tc2 <- map_concept mor c2
			return $ DLOr tc1 tc2
	DLNot c1 -> 
		do 
			tc1 <- map_concept mor c1
			return $ DLNot tc1
	DLOneOf cs ->
		do 
			tcs <- mapM (\x -> Map.lookup x $ c_map mor) cs
			return $ DLOneOf tcs
                
type DLRel = DLConcept

data DLClassProperty = DLSubClassof [DLConcept]
                     | DLEquivalentTo [DLConcept]
                     | DLDisjointWith [DLConcept]
                     deriving (Ord, Eq)

data DLBasicItem = DLClass  Id [DLClassProperty] (Maybe DLPara)|
                   DLValPart Id [Id] (Maybe DLPara)|
                   DLObjectProperty Id (Maybe Id) (Maybe Id)
                                        [DLPropsRel] [DLChars] (Maybe DLPara)|
                   DLDataProperty Id (Maybe Id) (Maybe Id) 
                                      [DLPropsRel] (Maybe DLChars) (Maybe DLPara) |                                       
                   DLIndividual Id (Maybe DLType) [DLFacts]
                                    [DLIndRel] (Maybe DLPara)
                   deriving (Ord, Eq)

data DLFacts = DLPosFact (Id,Id) | DLNegFact (Id,Id)
             deriving (Ord, Eq)

data DLType = DLType [Id]
              deriving (Ord, Eq)

data DLChars = DLFunctional | DLInvFuntional | DLSymmetric | DLTransitive
             deriving (Ord, Eq)

data DLIndRel = DLDifferentFrom [Id] |
                DLSameAs [Id]
                deriving (Ord, Eq)

data DLPropsRel = DLSubProperty [Id] |
                  DLInverses [Id]    |
                  DLEquivalent [Id]  |
                  DLDisjoint [Id]
                  deriving (Ord, Eq)

type ISOLangCode = String

data DLPara = DLPara [(ISOLangCode, String)]
					deriving (Ord, Eq)

data DLBasic = DLBasic [DLBasicItem]

map_sentence :: DLMorphism -> DLBasicItem -> Result.Result DLBasicItem
map_sentence mor sen = do return sen

-- A lot of pretty printing stuff

instance Pretty DLBasicItem where
    pretty = text . show

instance Pretty DLClassProperty where
    pretty = text . show

instance Pretty DLBasic where
    pretty = text . show

instance Pretty DLConcept where
    pretty = text . show

printDLConcept :: DLConcept -> String
printDLConcept con = case con of
	DLClassId cid -> show cid
	DLAnd c1 c2   -> (show c1) ++ " and " ++ (show c2)
	DLOr c1 c2   -> (show c1) ++ " or " ++ (show c2)
	DLXor c1 c2   -> (show c1) ++ " xor " ++ (show c2)
	DLNot c1 -> "not " ++ (show c1)
	DLOneOf cs -> "{" ++ concatSpace (map show cs) ++ "}"
	DLSome r c -> show r ++ " some " ++ show c
	DLHas r c -> show r ++ " has " ++ show c
	DLOnly r c -> show r ++ " only " ++ show c
	DLMin c i -> show c ++ " min " ++ show i
	DLMax c i -> show c ++ " max " ++ show i
	DLExactly c i -> show c ++ " exactly " ++ show i
	DLValue c i -> show c ++ " value " ++ show i	
	DLThat c1 c2   -> (show c1) ++ " that " ++ (show c2)
	DLOnlysome c cs -> (show c) ++ " onlysome " ++ (concatSpace $ map show cs)

printDLClassProperty :: DLClassProperty -> String
printDLClassProperty cp = case cp of
	DLSubClassof cs -> "SubclassOf: " ++ (concatComma $ map show cs)
	DLEquivalentTo cs -> "EquivalentTo: " ++ (concatComma $ map show cs)
	DLDisjointWith cs -> "DisjointWith: " ++ (concatComma $ map show cs)

printDLBasicItem :: DLBasicItem -> String
printDLBasicItem bi = case bi of
	DLClass cid cprops mpara -> 
		case mpara of
			Nothing -> "Class: " ++ show cid ++ "\n" ++ concatNL (map show cprops) ++ "\n"
			Just pa -> "Class: " ++ show cid ++ "\n" ++ concatNL (map show cprops) ++ show pa ++ "\n"
	DLValPart cid v para -> "ValuePartition: " ++ show cid ++ " [ " ++ 
								concatComma (map show v) ++ " ] " ++
								(case para of
									Nothing -> ""
									Just x  -> " " ++ show x ++ " ") ++ "\n"
	DLObjectProperty cid dom rn propsRel chars para ->
		"ObjectProperty: " ++ show cid ++ showMaybe "\nDomain: " dom ++ 
		showMaybe "\nRange: " rn ++ "\n" ++ concatNL (map show propsRel) ++ "\n" ++
		concatNL (map show chars) ++ showMaybe "\nParaphrase: " para
	DLDataProperty cid dom rn propsRel chars para ->
		"DataProperty: " ++ show cid ++ showMaybe "\nDomain: " dom ++ 
		showMaybe "\nRange: " rn ++ "\n" ++ concatNL (map show propsRel) ++ 
		showMaybe "\nCharacteristics: " chars ++ showMaybe "\nParaphrase: " para		
	DLIndividual cid tp fts indRel para -> 
		"Individual: " ++ show cid ++ showMaybe "\nType: " tp ++ 
			(case fts of
				[] -> ""
				_  -> "\nFacts: " ++ concatComma (map show fts)) ++ "\n" ++
		concatNL (map show indRel) ++ showMaybe "\nParaphrase: " para

printFact :: DLFacts -> String
printFact fct = case fct of
	DLPosFact (a, b) -> show a ++ " " ++ show b
	DLNegFact (a, b) -> "not " ++ show a ++ " " ++ show b

showDLType :: DLType -> String
showDLType (DLType t) = concatComma $ map show t

printDLChars :: DLChars -> String
printDLChars dc = case dc of
	DLFunctional -> "Functional"
	DLInvFuntional -> "InverseFunctional"
	DLSymmetric -> "Symmetric"
	DLTransitive -> "Transitive"

printDLIndRel :: DLIndRel -> String
printDLIndRel ir = case ir of
	DLDifferentFrom ci -> "DifferentFrom: " ++ (concatComma $ map show ci)
	DLSameAs ci        -> "SameAs: " ++ (concatComma $ map show ci)

printPropsRel :: DLPropsRel -> String
printPropsRel r = case r of
	DLSubProperty p -> "SubpropertyOf: " ++ (concatComma $ map show p)
	DLInverses p    -> "Inverses: " ++ (concatComma $ map show p)
	DLEquivalent p  -> "Equivalent: " ++ (concatComma $ map show p)
	DLDisjoint p    -> "Disjoint: " ++ (concatComma $ map show p)	


printDLPara :: DLPara -> String
printDLPara p = case p of
	DLPara cs -> concatNL $ map 
		(\(x, y) -> show y ++ " [lang: " ++ show x ++"] ") cs

printBasic :: DLBasic -> String
printBasic (DLBasic bs) = concatNL $ map show bs

instance Show DLBasic where
	show = printBasic

instance Show DLPara where
	show = printDLPara

instance Show DLPropsRel where
	show = printPropsRel

instance Show DLIndRel where
	show = printDLIndRel

instance Show DLChars where
	show = printDLChars

instance Show DLType where
	show = showDLType

instance Show DLFacts where
	show = printFact
	
instance Show DLConcept where
	show = printDLConcept
	
instance Show DLClassProperty where
	show = printDLClassProperty

instance Show DLBasicItem where
	show = printDLBasicItem

concatSpace :: [String] -> String
concatSpace [] = ""
concatSpace (x:[]) = x
concatSpace (x:xs) = x ++ " " ++ concatSpace xs

concatNL :: [String] -> String
concatNL [] = ""
concatNL (x:[]) = x
concatNL (x:xs) = x ++ "\n" ++ concatSpace xs

showMaybe :: (Show x) => String -> Maybe x -> String
showMaybe st m = case m of 
	Nothing -> ""
	Just x  -> st ++ show x
	
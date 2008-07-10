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
                DLEquality(..),
                DLPropertyComp(..),
                concatComma,
                expand)
                        where

import Common.Id
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import DL.DLKeywords

-- DrIFT command
{-! global: GetRange !-}

data DLConcept = DLClassId Id Range|
               DLAnd DLConcept DLConcept Range|
               DLOr DLConcept DLConcept Range|
               DLNot DLConcept Range|
               DLOneOf [Id] Range|
               DLSome DLRel DLConcept Range|
               DLHas DLRel Id Range|       -- Id is the Id of an individual
               DLOnly DLRel DLConcept Range|
               DLMin DLRel Int (Maybe DLConcept) Range|
               DLMax DLRel Int (Maybe DLConcept) Range|
               DLExactly DLRel Int (Maybe DLConcept) Range|
               DLValue DLRel Id Range|
               DLOnlysome DLRel [DLConcept] Range|
               DLXor DLConcept DLConcept Range |
               DLSelf Range
               deriving (Ord, Eq)

type DLRel = Id  -- Data and Object Properties are relations

data DLClassProperty = DLSubClassof [DLConcept] Range
                     | DLEquivalentTo [DLConcept] Range
                     | DLDisjointWith [DLConcept] Range
                     deriving (Ord, Eq)

data DLFacts = DLPosFact (Id,Id) Range | DLNegFact (Id,Id) Range
             deriving (Ord, Eq)

data DLType = DLType [Id] Range
              deriving (Ord, Eq)

data DLChars = DLFunctional | DLInvFuntional | DLSymmetric | DLTransitive |
               DLReflexive | DLIrreflexive
             deriving (Ord, Eq)

data DLIndRel = DLDifferentFrom [Id] Range |
                DLSameAs [Id] Range
                deriving (Ord, Eq)

data DLPropsRel = DLSubProperty [Id] Range|
                  DLInverses [Id]    Range|
                  DLEquivalent [Id]  Range|
                  DLDisjoint [Id]    Range|
                  DLSuperProperty  [DLPropertyComp] Range
                  deriving (Ord, Eq)

type ISOLangCode = String

data DLEquality = DLDifferent | DLSame
                  deriving (Ord,Eq)

data DLPara = DLPara [(ISOLangCode, String)] Range
                    deriving (Ord, Eq)

data DLBasicItem = DLClass  Id [DLClassProperty] (Maybe DLPara) Range|
                   DLObjectProperty Id (Maybe DLConcept) (Maybe DLConcept)
                                        [DLPropsRel] [DLChars] (Maybe DLPara) Range|
                   DLDataProperty Id (Maybe DLConcept) (Maybe DLConcept)
                                      [DLPropsRel] (Maybe DLChars) (Maybe DLPara) Range |
                   DLIndividual Id (Maybe DLType) [DLFacts]
                                    [DLIndRel] (Maybe DLPara) Range|
                   DLMultiIndi [Id] (Maybe DLType) [DLFacts] (Maybe DLEquality) (Maybe DLPara) Range
                   deriving (Ord, Eq)

data DLPropertyComp = DLPropertyComp [Id]
                        deriving (Eq, Ord)


data DLBasic = DLBasic [Annoted (DLBasicItem)]

-- ^ Function to expand macros in Concepts like onlysome
expand :: DLConcept -> DLConcept
expand c =
    case c of
      DLOnlysome r c1 rn -> expandDLOnlysome r c1 rn
      _                  -> c

expandDLOnlysome :: DLRel -> [DLConcept] -> Range-> DLConcept
expandDLOnlysome r c rn =
    let
        ro = foldl (\x y -> DLAnd x y rn) (head $ map (\x -> DLSome r x rn) c) (tail $ map (\x -> DLSome r x rn) c)
        oO = DLOnly r (foldl (\x y -> DLOr  x y rn) (head $ c) (tail $ c)) rn
    in
      DLAnd ro oO rn

-- A lot of pretty printing stuff
instance Pretty DLBasicItem where
    pretty = text . show

instance Pretty DLClassProperty where
    pretty = text . show

instance Pretty DLBasic where
    pretty = text . show

instance Pretty DLConcept where
    pretty = text . show

instance Pretty DLEquality where
    pretty = text . show

instance Show DLEquality where
    show = printDLEquality

instance Show DLPropertyComp where
    show = showPropertyComp

printDLEquality :: DLEquality -> String
printDLEquality eq = case eq of
    DLDifferent -> "Different"
    DLSame -> "Same"

printDLConcept :: DLConcept -> String
printDLConcept con = "(" ++ (case con of
        DLClassId cid _-> show cid
        DLAnd c1 c2   _-> (show c1) ++ " and " ++ (show c2)
        DLOr c1 c2   _-> (show c1) ++ " or " ++ (show c2)
        DLXor c1 c2   _-> (show c1) ++ " xor " ++ (show c2)
        DLNot c1 _-> "not " ++ (show c1)
        DLOneOf cs _-> "{" ++ concatSpace (map show cs) ++ "}"
        DLSome r c _-> show r ++ " some " ++ show c
        DLHas r c _-> show r ++ " has " ++ show c
        DLOnly r c _-> show r ++ " only " ++ show c
        DLMin c i cp _-> show c ++ " min " ++ show i ++ " " ++ showMCt cp
        DLMax c i cp _-> show c ++ " max " ++ show i ++ " " ++ showMCt cp
        DLExactly c i cp _-> show c ++ " exactly " ++ show i ++ " " ++ showMCt cp
        DLValue c i _-> show c ++ " value " ++ show i
        DLOnlysome c cs _-> (show c) ++ " onlysome [" ++ (concatSpace $  map show cs) ++"]"
        --DLOnlysome c cs _-> show (expand $ DLOnlysome c cs nullRange)
        DLSelf _ -> dlSelf) ++ ")"

showMCt :: Maybe DLConcept -> String
showMCt ct =
    case ct of
        Nothing -> ""
        Just x  -> show x

printDLClassProperty :: DLClassProperty -> String
printDLClassProperty cp = case cp of
        DLSubClassof cs _-> "SubclassOf: " ++ (concatComma $ map show cs)
        DLEquivalentTo cs _-> "EquivalentTo: " ++ (concatComma $ map show cs)
        DLDisjointWith cs _-> "DisjointWith: " ++ (concatComma $ map show cs)

printDLBasicItem :: DLBasicItem -> String
printDLBasicItem bi = case bi of
    DLClass cid cprops mpara _ ->
        case mpara of
            Nothing -> "Class: " ++ show cid ++ "\n" ++ concatNL (map show cprops) ++ "\n"
            Just pa -> "Class: " ++ show cid ++ "\n" ++ concatNL (map show cprops) ++ "\nParaphrase: " ++ show pa ++ "\n"
    DLObjectProperty cid dom rn propsRel chars para _ ->
        "ObjectProperty: " ++ show cid ++ showMaybe "\nDomain: " dom ++
        showMaybe "\nRange: " rn ++ "\n" ++ concatNL (map show propsRel) ++ (if (chars /= []) then "Characteristics: " else "") ++
        concatComma (map show chars) ++ showMaybe "\nParaphrase: " para
    DLDataProperty cid dom rn propsRel chars para _ ->
        "DataProperty: " ++ show cid ++ showMaybe "\nDomain: " dom ++
        showMaybe "\nRange: " rn ++ "\n" ++ concatNL (map show propsRel) ++
        showMaybe "\nCharacteristics: " chars ++ showMaybe "\nParaphrase: " para
    DLIndividual cid tp fts indRel para _ ->
        "Individual: " ++ show cid ++ showMaybe "\nType: " tp ++
            (case fts of
                [] -> ""
                _  -> "\nFacts: " ++ concatComma (map show fts)) ++ "\n" ++
        concatNL (map show indRel) ++ showMaybe "\nParaphrase: " para
    DLMultiIndi idList tp fts equl para _ ->
        "Individuals: " ++ concatComma (map show idList) ++
            showMaybe "\nType: " tp ++
            (case fts of
                [] -> ""
                _  -> "\nFacts: " ++ concatComma (map show fts)) ++
                showMaybe "\nEquality: " equl ++ showMaybe "\nParaphrase: " para

printFact :: DLFacts -> String
printFact fct = case fct of
        DLPosFact (a, b) _-> show a ++ " " ++ show b
        DLNegFact (a, b) _-> "not " ++ show a ++ " " ++ show b

showDLType :: DLType -> String
showDLType (DLType t _) = concatComma $ map show t

printDLChars :: DLChars -> String
printDLChars dc = case dc of
        DLFunctional -> dlFunc
        DLInvFuntional -> dlInvFunc
        DLSymmetric -> dlSym
        DLTransitive -> dlTrans
        DLReflexive -> dlRefl
        DLIrreflexive -> dlIrr

printDLIndRel :: DLIndRel -> String
printDLIndRel ir = case ir of
        DLDifferentFrom ci _-> "DifferentFrom: " ++ (concatComma $ map show ci)
        DLSameAs ci        _-> "SameAs: " ++ (concatComma $ map show ci)

printPropsRel :: DLPropsRel -> String
printPropsRel r = case r of
        DLSubProperty p _-> "SubpropertyOf: " ++ (concatComma $ map show p)
        DLInverses p    _-> "Inverses: " ++ (concatComma $ map show p)
        DLEquivalent p  _-> "Equivalent: " ++ (concatComma $ map show p)
        DLDisjoint p    _-> "Disjoint: " ++ (concatComma $ map show p)
        DLSuperProperty p _ -> "SuperpropertyOf:" ++ (concatComma $ map show p)

printDLPara :: DLPara -> String
printDLPara p = case p of
        DLPara cs _-> concatNL $ map
                (\(x, y) -> "\"" ++ y  ++ "\" [lang: " ++ x ++"] ") cs

printBasic :: DLBasic -> String
printBasic (DLBasic bs) = concatNL $ map show bs

showPropertyComp ::DLPropertyComp -> String
showPropertyComp cmp =
    case cmp of
        DLPropertyComp iid -> concatSemi $ map show iid

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

concatComma :: [String] -> String
concatComma [] = ""
concatComma (x:[]) = x
concatComma (x:xs) = x ++ ", " ++ concatComma xs

concatSemi :: [String] -> String
concatSemi [] = ""
concatSemi (x:[]) = x
concatSemi (x:xs) = x ++ " ; " ++ concatSemi xs


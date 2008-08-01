{- |
Module      :  $Header$
Description :  Keywords for DL logic
Copyright   :  Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Keywords for the DL Concrete Syntax
-}

module DL.DLKeywords where

dlclass :: String
dlclass = "Class:"

dlxor :: String
dlxor = "xor"

dlor :: String
dlor = "or"

dland :: String
dland = "and"

dlnot :: String
dlnot = "not"

dlthat :: String
dlthat = "that"

dlsome :: String
dlsome = "some"

dlonly :: String
dlonly = "only"

dlmin :: String
dlmin = "min"

dlmax :: String
dlmax = "max"

dlexact :: String
dlexact = "exactly"

dlvalue :: String
dlvalue = "value"

dlhas :: String
dlhas = "has"

dlonlysome :: String
dlonlysome = "onlysome"

dlSub :: String
dlSub = "SubclassOf:"

dlEquivTo :: String
dlEquivTo = "EquivalentTo:"

dlInv :: String
dlInv = "Inverses:"

dlInvOf :: String
dlInvOf = "InverseOf:"

dlDisjoint :: String
dlDisjoint = "DisjointWith:"

dlDis :: String
dlDis = "Disjoint:"

dlDomain :: String
dlDomain = "Domain:"

dlRange :: String
dlRange = "Range:"

dlValPart :: String
dlValPart = "ValuePartition:"

dlObjProp :: String
dlObjProp = "ObjectProperty:"

dlChar :: String
dlChar = "Characteristics:"

dlInvFunc :: String
dlInvFunc = "InverseFunctional"

dlFunc :: String
dlFunc = "Functional"

dlSame :: String
dlSame = "SameAs:"

dlEquiv :: String
dlEquiv = "Equivalent:"

dlSym :: String
dlSym = "Symmetric"

dlTrans :: String
dlTrans = "Transitive"

dlDataProp :: String
dlDataProp = "DataProperty:"

dlPara :: String
dlPara = "Paraphrase:"

dlIndi :: String
dlIndi = "Individual:"

dlSubProp :: String
dlSubProp = "SubPropertyOf:"

dlTypes :: String
dlTypes = "Types:"

dlFacts :: String
dlFacts = "Facts:"

dlDiff :: String
dlDiff = "DifferentFrom:"

dlLang :: String
dlLang = "lang"

dlMultiIndi :: String
dlMultiIndi = "Individuals:"

dlEquality :: String
dlEquality = "Equality:"

dlEqualI :: String
dlEqualI = "Same"

dlDiffI :: String
dlDiffI = "Different"

dlThing :: String
dlThing = "Thing"

dlNothing :: String
dlNothing = "Nothing"

dlData :: String
dlData = "DATA"

dlInteger :: String
dlInteger = "integer"

dlNonPosInt :: String
dlNonPosInt = "nonPositiveInteger"

dlNonNegInt :: String
dlNonNegInt = "nonNegativeInteger"

dlPosInt :: String
dlPosInt = "positiveInteger"

dlNegInt :: String
dlNegInt = "negativeInteger"

dlBool :: String
dlBool = "boolean"

dlType :: String
dlType = "Type:"

dlRefl :: String
dlRefl = "Reflexive"

dlIrr :: String
dlIrr = "Irreflexive"

dlSuperProp :: String
dlSuperProp = "SuperpropertyOf:"

dlSelf :: String
dlSelf = "Self"

dlUniversal :: String
dlUniversal = "Universal"
dlString :: String
dlString = "string"

casl_dl_keywords :: [String]
casl_dl_keywords = [dlclass, dlxor, dlor, dland, dlnot, dlthat, dlsome,
                    dlonly, dlmin, dlmax, dlexact, dlvalue, dlhas,
                    dlonlysome, dlSub, dlEquivTo, dlInv, dlInvOf,dlFacts,
                    dlDisjoint,dlDomain,dlRange,dlValPart,
                    dlObjProp,dlChar,dlInvFunc,dlTypes,dlDiff,
                    dlSame,dlEquiv,dlSym,dlTrans, dlDataProp,
                    dlPara, dlIndi, dlFunc, dlSubProp,dlDis,dlLang,
                    dlMultiIndi, dlEquality, dlEqualI, dlDiffI, dlType,
                    dlRefl, dlIrr, dlSuperProp, dlSelf
                    ]

{- |
Module      :  $Header$
Description :  Signature for THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Data structures and functions for thf THF Signatures.
Note: Most of the implenentations support only THF0.
-}

module THF.Sign where

import THF.As
import THF.Cons

import Common.DefaultMorphism
import Common.Id
import Common.Result

import qualified Data.Map as Map

-- We use the DefaultMorphism for THF.
type MorphismTHF = DefaultMorphism SignTHF

data SignTHF = Sign
    { types     :: TypeMap
    , consts    :: ConstMap
    , symbols   :: SymbolMap
    } deriving (Show, Eq)

instance Ord SignTHF where
    compare s1 s2 = compare
        (types s1, consts s1)
        (types s2, consts s2)

instance GetRange SignTHF

type TypeMap = Map.Map Constant TypeInfo

type ConstMap = Map.Map Constant ConstInfo

type SymbolMap = Map.Map Constant SymbolTHF

data TypeInfo = TypeInfo
    { typeName  :: Constant
    , typeKind  :: Kind
    , typeDef   :: Maybe THFTypedConst }
    deriving (Show, Ord, Eq)

data ConstInfo = ConstInfo
    { constName :: Constant
    , constType :: Type
    , constDef  :: Maybe THFTypedConst }
    deriving (Show, Ord, Eq)

-- Creates an empty Signature.
emptySign :: SignTHF
emptySign = Sign
    { types     = Map.empty
    , consts    = Map.empty
    , symbols   = Map.empty }

-- Union of two signatures
-- The globAnnos will be taken from the first signature
sigUnion :: SignTHF -> SignTHF -> Result SignTHF
sigUnion s1 s2 =
    let smu = symbolMapUnion (symbols s1) (symbols s2)
    in case smu of
        Right d     -> Result [d] Nothing
        Left nsm    ->
            let tmu = typeMapUnion (types s1) (types s2)
                cmu = constMapUnion (consts s1) (consts s2)
            in case tmu of
                Right d1    -> Result [d1] Nothing
                Left ntm     -> case cmu of
                    Right d2    -> Result [d2] Nothing
                    Left ncm     -> Result [] (Just $
                        s1 { types = ntm, consts = ncm, symbols = nsm })

typeMapUnion :: TypeMap -> TypeMap -> Either TypeMap Diagnosis
typeMapUnion = error "typeMapUnion not implementet yet."

constMapUnion :: ConstMap -> ConstMap -> Either ConstMap Diagnosis
constMapUnion = error "constMapUnion not implementet yet."

symbolMapUnion :: SymbolMap -> SymbolMap -> Either SymbolMap Diagnosis
symbolMapUnion = error "symbolMapUnion not implementet yet."

-- Difference of two signatures
-- The globAnnos will be taken from the first signature
sigDiff :: SignTHF -> SignTHF -> Result SignTHF
sigDiff s1 s2 =
    let smd = symbolMapDiff (symbols s1) (symbols s2)
    in case smd of
        Right d     -> Result [d] Nothing
        Left nsm    ->
            let tmd = typeMapDiff (types s1) (types s2)
                cmd = constMapDiff (consts s1) (consts s2)
            in case tmd of
                Right d1    -> Result [d1] Nothing
                Left ntm    -> case cmd of
                    Right d2    -> Result [d2] Nothing
                    Left ncm    -> Result [] (Just $
                        s1 { types = ntm, consts = ncm, symbols = nsm })

typeMapDiff :: TypeMap -> TypeMap -> Either TypeMap Diagnosis
typeMapDiff = error "typeMapDiff not implementet yet."

constMapDiff :: ConstMap -> ConstMap -> Either ConstMap Diagnosis
constMapDiff = error "constMapDiff not implementet yet."

symbolMapDiff :: SymbolMap -> SymbolMap -> Either SymbolMap Diagnosis
symbolMapDiff = error "symbolSetDiff not implementet yet."

-- Insersectin of two signatures
-- The globAnnos will be taken from the first signature
sigIntersect :: SignTHF -> SignTHF -> Result SignTHF
sigIntersect s1 s2 =
    let smi = symbolMapIntersect (symbols s1) (symbols s2)
    in case smi of
        Right d     -> Result [d] Nothing
        Left nsm    ->
            let tmi = typeMapIntersect (types s1) (types s2)
                cmi = constMapIntersect (consts s1) (consts s2)
            in case tmi of
                Right d1    -> Result [d1] Nothing
                Left ntm    -> case cmi of
                    Right d2    -> Result [d2] Nothing
                    Left ncm    -> Result [] (Just $
                        s1 { types = ntm, consts = ncm, symbols = nsm })

typeMapIntersect :: TypeMap -> TypeMap -> Either TypeMap Diagnosis
typeMapIntersect = error "typeMapIntersection not implementet yet."

constMapIntersect :: ConstMap -> ConstMap -> Either ConstMap Diagnosis
constMapIntersect = error "constMapIntersection not implementet yet."

symbolMapIntersect :: SymbolMap -> SymbolMap -> Either SymbolMap Diagnosis
symbolMapIntersect = error "symbolSetIntersection not implementet yet."

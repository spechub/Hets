{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./THF/Sign.hs
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
import Common.Id hiding (typeId)
import Common.Result

import Data.Data
import qualified Data.HashMap.Strict as Map

import GHC.Generics (Generic)
import Data.Hashable

{- -----------------------------------------------------------------------------
Definitions and instances of data structures
----------------------------------------------------------------------------- -}

-- We use the DefaultMorphism for THF.
type MorphismTHF = DefaultMorphism SignTHF

{- A signature is a container for types and constants. In addition they are
stored in an SymbolMap. -}
data SignTHF = Sign
    { types :: TypeMap
    , consts :: ConstMap
    , symbols :: SymbolMap
    } deriving (Show, Eq, Typeable, Data)

-- Ord instance that does not use symbols
instance Ord SignTHF where
    compare s1 s2 = compare (types s1, consts s1) (types s2, consts s2)

instance GetRange SignTHF

-- Map for Types.
type TypeMap = Map.HashMap Constant TypeInfo

-- Map for Constants.
type ConstMap = Map.HashMap Constant ConstInfo

-- Map for Symbols. These are symbols and types.
type SymbolMap = Map.HashMap Constant SymbolTHF

{- TypeInfo are containers for types, their name and Kind.
In addition the original Annotaions can be stored as
Annotations. -}
data TypeInfo = TypeInfo
    { typeId :: Constant
    , typeName :: Name
    , typeKind :: Kind
    , typeAnno :: Annotations }
    deriving (Show, Typeable, Data, Generic)

instance Hashable TypeInfo

-- Ord instance that neither uses typeDef nor typeAnno
instance Ord TypeInfo where
    compare ti1 ti2 = compare
        (typeId ti1, typeName ti1, typeKind ti1)
        (typeId ti2, typeName ti2, typeKind ti2)

-- Eq instance that neither uses typeDef nor typeAnno
instance Eq TypeInfo where
    (==) ti1 ti2 = (typeId ti1, typeName ti1, typeKind ti1) ==
                   (typeId ti2, typeName ti2, typeKind ti2)

{- ConstInfo are containers for constants, their naem and type.
In addition the original Annotaions can be stored as
Annotations. -}
data ConstInfo = ConstInfo
    { constId :: Constant
    , constName :: Name
    , constType :: Type
    , constAnno :: Annotations }
    deriving (Show, Typeable, Data, Generic)

instance Hashable ConstInfo

-- Ord instance that neither uses constDef nor constAnno
instance Ord ConstInfo where
    compare ci1 ci2 = compare
        (constId ci1, constName ci1, constType ci1)
        (constId ci2, constName ci2, constType ci2)

-- Eq instance that neither uses constDef nor constAnno
instance Eq ConstInfo where
    (==) ci1 ci2 = (constId ci1, constName ci1, constType ci1) ==
                   (constId ci2, constName ci2, constType ci2)

-- Creates an empty Signature.
emptySign :: SignTHF
emptySign = Sign
    { types = Map.empty
    , consts = Map.empty
    , symbols = Map.empty }


{- -----------------------------------------------------------------------------
Some helper data structures and functions for the
union, difference and insersection methods
----------------------------------------------------------------------------- -}

type EitherMap c x = Map.HashMap c (Either x Diagnosis)

-- Convert a map into an EitherMap.
toEitherLeftMap :: Map.HashMap c x -> EitherMap c x
toEitherLeftMap = Map.map Left

eitherMapHasDiagnosis :: EitherMap c x -> Bool
eitherMapHasDiagnosis = Map.foldr (\ a b -> case a of
    Right _ -> True
    _ -> b ) False

-- only use after eitherMapHasDiagnosis returned true
eitherMapGetDiagnosis :: EitherMap c x -> [Diagnosis]
eitherMapGetDiagnosis =
    Map.foldr (\ e dl -> either (const dl) (: dl) e) []

-- only use after eitherMapHasDiagnosis returned false
eitherMapGetMap :: EitherMap c x -> Map.HashMap c x
eitherMapGetMap = Map.map (\ (Left a) -> a)

{- If the EitherMap contains diagnosis they will be returned in a list.
Otherwise the map will be converted back. -}
genRes :: EitherMap c x -> Either (Map.HashMap c x) [Diagnosis]
genRes em = if eitherMapHasDiagnosis em
            then Right (eitherMapGetDiagnosis em)
            else Left (eitherMapGetMap em)


{- -----------------------------------------------------------------------------
Signature union
----------------------------------------------------------------------------- -}

-- Union of two signatures
sigUnion :: SignTHF -> SignTHF -> Result SignTHF
sigUnion s1 s2 =
    let smu = symbolMapUnion (symbols s1) (symbols s2)
    in case smu of
        Right d -> Result d Nothing
        Left nsm ->
            let tmu = typeMapUnion (types s1) (types s2)
                cmu = constMapUnion (consts s1) (consts s2)
            in case tmu of
                Right d1 -> Result d1 Nothing
                Left ntm -> case cmu of
                    Right d2 -> Result d2 Nothing
                    Left ncm -> Result [] (Just $
                        s1 { types = ntm, consts = ncm, symbols = nsm })

typeMapUnion :: TypeMap -> TypeMap -> Either TypeMap [Diagnosis]
typeMapUnion t1 t2 =
    let emt1 = toEitherLeftMap t1
        emt2 = toEitherLeftMap t2
    in genRes $ unite "Types" emt1 emt2

constMapUnion :: ConstMap -> ConstMap -> Either ConstMap [Diagnosis]
constMapUnion c1 c2 =
    let emc1 = toEitherLeftMap c1
        emc2 = toEitherLeftMap c2
    in genRes $ unite "Constants" emc1 emc2

symbolMapUnion :: SymbolMap -> SymbolMap -> Either SymbolMap [Diagnosis]
symbolMapUnion s1 s2 =
    let ems1 = toEitherLeftMap s1
        ems2 = toEitherLeftMap s2
    in genRes $ unite "Symbols" ems1 ems2

unite :: (Ord c, Eq x, Show x, Hashable c) => String -> EitherMap c x -> EitherMap c x
                                                          -> EitherMap c x
unite s = Map.unionWith (\ (Left e1) (Left e2) -> if e1 == e2 then Left e1
            else Right (mkDiag Error
                    (s ++ " " ++ show e1 ++ " and " ++ show e2 ++
                    " have the same name but heve different definitions.") ()))


{- -----------------------------------------------------------------------------
Signature difference
----------------------------------------------------------------------------- -}

-- Difference of two signatures
sigDiff :: SignTHF -> SignTHF -> Result SignTHF
sigDiff s1 s2 = Result [] (Just $
    s1 { types = diff (types s1) (types s2)
       , consts = diff (consts s1) (consts s2)
       , symbols = diff (symbols s1) (symbols s2) })

diff :: (Ord c, Eq x, Hashable c) => Map.HashMap c x -> Map.HashMap c x -> Map.HashMap c x
diff = Map.differenceWith (\ e1 e2 -> if e1 == e2 then Nothing else Just e1)

{- -----------------------------------------------------------------------------
Signature intersection
----------------------------------------------------------------------------- -}

-- Intersection of two signatures
sigIntersect :: SignTHF -> SignTHF -> Result SignTHF
sigIntersect s1 s2 =
    let smi = symbolMapIntersect (symbols s1) (symbols s2)
    in case smi of
        Right d -> Result d Nothing
        Left nsm ->
            let tmi = typeMapIntersect (types s1) (types s2)
                cmi = constMapIntersect (consts s1) (consts s2)
            in case tmi of
                Right d1 -> Result d1 Nothing
                Left ntm -> case cmi of
                    Right d2 -> Result d2 Nothing
                    Left ncm -> Result [] (Just $
                        s1 { types = ntm, consts = ncm, symbols = nsm })

typeMapIntersect :: TypeMap -> TypeMap -> Either TypeMap [Diagnosis]
typeMapIntersect t1 t2 =
    let emt1 = toEitherLeftMap t1
        emt2 = toEitherLeftMap t2
    in genRes $ intersect "Types" emt1 emt2

constMapIntersect :: ConstMap -> ConstMap -> Either ConstMap [Diagnosis]
constMapIntersect c1 c2 =
    let emc1 = toEitherLeftMap c1
        emc2 = toEitherLeftMap c2
    in genRes $ intersect "Constants" emc1 emc2

symbolMapIntersect :: SymbolMap -> SymbolMap -> Either SymbolMap [Diagnosis]
symbolMapIntersect s1 s2 =
    let ems1 = toEitherLeftMap s1
        ems2 = toEitherLeftMap s2
    in genRes $ intersect "Symbols" ems1 ems2

intersect :: (Ord c, Eq x, Show x, Hashable c) => String -> EitherMap c x -> EitherMap c x
                                                         -> EitherMap c x
intersect s = Map.intersectionWith (\ (Left e1) (Left e2) ->
                if e1 == e2 then Left e1 else Right (mkDiag Error
                    (s ++ " " ++ show e1 ++ " and " ++ show e2 ++
                    " have the same name but heve different definitions.") ()))

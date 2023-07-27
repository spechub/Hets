{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/Sign.hs
Description :  Data structures representing TPTP signatures.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Data structures representing TPTP signatures.
-}

module TPTP.Sign where

import TPTP.AS

import Common.Id

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

type Sentence = Annotated_formula

data Symbol = Symbol { symbolId :: Token
                     , symbolType :: SymbolType
                     } deriving (Show, Ord, Eq, Data, Typeable)

instance GetRange Symbol where
  getRange = Range . rangeSpan
  rangeSpan = tokenRange . symbolId

data SymbolType = Constant
                | Number
                | Predicate
                | Proposition
                | Function
                | TypeConstant
                | TypeFunctor
                  deriving (Show, Ord, Eq, Data, Typeable)

instance GetRange SymbolType

symbolTypeS :: Symbol -> String
symbolTypeS = show . symbolType

type ConstantSet = Set.Set Constant
type FunctorMap = Map.Map TPTP_functor FunctorType
type NumberSet = Set.Set Number
type PropositionSet = Set.Set Proposition
type THFTypeDeclarationMap = Map.Map THFTypeable THF_top_level_type
type TFFTypeDeclarationMap = Map.Map Untyped_atom TFF_top_level_type
type THFPredicateMap = THFTypeDeclarationMap
type TFFPredicateMap = TFFTypeDeclarationMap
type FOFPredicateMap = Map.Map Predicate (Set.Set Int)
type FOFFunctorMap = Map.Map TPTP_functor (Set.Set Int)
type THFTypeConstantMap = THFTypeDeclarationMap
type TFFTypeConstantMap = TFFTypeDeclarationMap
type THFTypeFunctorMap = THFTypeDeclarationMap
type TFFTypeFunctorMap = TFFTypeDeclarationMap
type THFSubTypeMap = Map.Map THF_atom THF_atom
type TFFSubTypeMap = Map.Map Untyped_atom Atom

data THFTypeable = THFTypeFormula THF_typeable_formula
                 | THFTypeConstant Constant
                   deriving (Show, Eq, Ord, Data, Typeable)

data FunctorType = FunctorTHF THF_arguments
                 | FunctorFOF FOF_arguments
                   deriving (Show, Eq, Ord, Data, Typeable)

data PredicateType = PredicateType FOF_arguments
                     deriving (Show, Eq, Ord, Data, Typeable)

data Type_functorType = Type_functorType TFF_type_arguments
                        deriving (Show, Eq, Ord, Data, Typeable)

data Sign = Sign { constantSet :: ConstantSet
                 , numberSet :: NumberSet
                 , propositionSet :: PropositionSet
                 , thfSubtypeMap :: THFSubTypeMap
                 , tffSubtypeMap :: TFFSubTypeMap
                 , thfPredicateMap :: THFPredicateMap
                 , tffPredicateMap :: TFFPredicateMap
                 , fofPredicateMap :: FOFPredicateMap
                 , fofFunctorMap :: FOFFunctorMap
                 , thfTypeConstantMap :: THFTypeConstantMap
                 , tffTypeConstantMap :: TFFTypeConstantMap
                 , thfTypeFunctorMap :: THFTypeFunctorMap
                 , tffTypeFunctorMap :: TFFTypeFunctorMap
                 -- The following maps are just temporary and ignored after
                 -- static analysis in favor of thfPreficateMap, thfTypeFunctorMap,
                 -- tffPredicateMap and tffTypeFunctorMap
                 , thfTypeDeclarationMap :: THFTypeDeclarationMap
                 , tffTypeDeclarationMap :: TFFTypeDeclarationMap
                 } deriving (Show, Eq, Ord, Data, Typeable)

emptySign :: Sign
emptySign = Sign { constantSet = Set.empty
                 , numberSet = Set.empty
                 , propositionSet = Set.empty
                 , thfSubtypeMap = Map.empty
                 , tffSubtypeMap = Map.empty
                 , thfPredicateMap = Map.empty
                 , tffPredicateMap = Map.empty
                 , fofPredicateMap = Map.empty
                 , fofFunctorMap = Map.empty
                 , thfTypeConstantMap = Map.empty
                 , tffTypeConstantMap = Map.empty
                 , thfTypeFunctorMap = Map.empty
                 , tffTypeFunctorMap = Map.empty
                 , thfTypeDeclarationMap = Map.empty
                 , tffTypeDeclarationMap = Map.empty
                 }

negateSentence :: Sentence -> Maybe Sentence
negateSentence sen = case sen of
  AF_THF_Annotated (THF_annotated n r f a) -> case negate_thf f of
    Nothing -> Nothing
    Just f' -> Just $ AF_THF_Annotated $ THF_annotated n r f' a
  AF_TFX_Annotated (TFX_annotated _ _ _ _) -> Nothing -- Todo: Check if this is possible somehow
  AF_TFF_Annotated (TFF_annotated n r f a) -> case negate_tff f of
    Nothing -> Nothing
    Just f' -> Just $ AF_TFF_Annotated $ TFF_annotated n r f' a
  AF_TCF_Annotated (TCF_annotated _ _ _ _) -> Nothing -- Todo: break out of TCF
  AF_FOF_Annotated (FOF_annotated n r f a) -> case negate_fof f of
    Nothing -> Nothing
    Just f' -> Just $ AF_FOF_Annotated $ FOF_annotated n r f' a
  AF_CNF_Annotated (CNF_annotated _ _ _ _) -> Nothing -- Todo: break out of CNF
  AF_TPI_Annotated (TPI_annotated n r f a) -> case negate_fof f of
    Nothing -> Nothing
    Just f' -> Just $ AF_TPI_Annotated $ TPI_annotated n r f' a
  where
    negate_thf :: THF_formula -> Maybe THF_formula
    negate_thf formula = case formula of
      THFF_logic lf ->
        Just $ THFF_logic $ THFLF_unitary $
          THFUF_unary $ THF_unary_formula (THFUC_unary NOT) lf
      _ -> Nothing

    negate_tff :: TFF_formula -> Maybe TFF_formula
    negate_tff formula = case formula of
     TFFF_logic lf -> Just $ TFFF_logic $ TFFLF_unitary $ TFFUF_unary $
       TFFUF_connective NOT $ TFFUF_logic lf
     _ -> Nothing

    negate_fof :: FOF_formula -> Maybe FOF_formula
    negate_fof formula = case formula of
      FOFF_logic lf -> Just $ FOFF_logic $ FOFLF_unitary $ FOFUF_unary $
        FOFUF_connective NOT $ FOFUF_logic lf
      _ -> Nothing

{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/GenTypes
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module GenHyb.GenTypes where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Id as Id
import Data.Data
import Common.AS_Annotation as AS_Anno
import Common.Doc
import Common.DocUtils
import qualified CASL.AS_Basic_CASL as CBasic


-- | generic hybrid signatures
data HSign sig = HSign {
                  baseSig :: sig,
                  noms :: Set.Set Id,
                  mods :: Map.Map Id Int}
  deriving (Show, Eq, Ord, Typeable, Data)


-- | generic hybrid signature morphisms
data HMorphism sig mor = HMorphism
  { source :: HSign sig
  , target :: HSign sig
  , baseMor :: mor
  , nomMap :: Map.Map Id Id
  , modMap :: Map.Map Id Id
  } deriving (Show, Eq, Ord, Typeable, Data)

-- | generic hybrid formulas

data HFORMULA sen symb_items raw_sym =
    Base_formula sen Id.Range -- add a Maybe String to handle multiple layers of hybridization
    -- base sentences
  | Negation (HFORMULA sen symb_items raw_sym) Id.Range
   -- pos: not
  | Conjunction [HFORMULA sen symb_items raw_sym] Id.Range
    -- pos: "/\"s
  | Disjunction [HFORMULA sen symb_items raw_sym] Id.Range
    -- pos: "\/"s
  | Implication (HFORMULA sen symb_items raw_sym) (HFORMULA sen symb_items raw_sym) Id.Range
    -- pos: "=>"
  | Equivalence (HFORMULA sen symb_items raw_sym) (HFORMULA sen symb_items raw_sym) Id.Range
    -- pos: "<=>"
  | Nominal String Bool Id.Token Id.Range -- the String is the optional qualification, leave empty for the topmost logic
                                          -- the bool flag is true for nominal variables! 
   -- nominals as sentences
  | AtState Id.Token (HFORMULA sen symb_items raw_sym) Id.Range -- TODO: add a string to the token for the qualification!
   -- at_i formulas
  | BoxFormula Id.Token (HFORMULA sen symb_items raw_sym) Id.Range -- TODO: add a string to the token for the qualification!
   -- pos: "< >"
  | DiamondFormula Id.Token (HFORMULA sen symb_items raw_sym) Id.Range -- TODO: add a string to the token for the qualification!
   -- pos: "[ ]"
  | QuantVarsParse HQUANT [symb_items] (HFORMULA sen symb_items raw_sym) Id.Range 
   -- pos: QUANTIFIER, semi colons, dot
  | QuantVars HQUANT [raw_sym] (HFORMULA sen symb_items raw_sym) Id.Range 
  | QuantNominals HQUANT [Id.Token] (HFORMULA sen symb_items raw_sym) Id.Range
    deriving (Show, Eq, Ord, Typeable, Data)

nomS, modS :: String
nomS = "nominal"
modS = "modality"

data HQUANT = HUniversal String | HExistential String -- the quantifier must have a logic identifier, and if it's empty it defaults to the current logic
                  deriving (Show, Eq, Ord, Typeable, Data)

-- | generic hybrid basic spec
data NOM_ITEM = Nom_item [Token] Range
               deriving (Show, Typeable, Data)

data MOD_ITEM = Mod_item [Token] Int Range
               deriving (Show, Typeable, Data)

data H_BASIC_ITEMS sen symb_items raw_sym =
      Nom_decl NOM_ITEM
    | Mod_decl MOD_ITEM
    | Axiom_items [AS_Anno.Annoted (HFORMULA sen symb_items raw_sym)]
  deriving (Show, Typeable, Data)

newtype H_BASIC_SPEC sen symb_items raw_sym = Basic_spec [AS_Anno.Annoted (H_BASIC_ITEMS sen symb_items raw_sym)]
                  deriving (Show, Typeable, Data)

-- | generic symb_items

data H_SYMB_KIND = NomKind | ModKind 
     deriving (Show, Eq, Ord, Typeable, Data)

data H_SYMB_ITEMS sym symb_items =  
                         BaseSymbItems symb_items
                       | HSymbItems H_SYMB_KIND [HSymbol sym] Id.Range
                  deriving (Show, Eq, Ord, Typeable, Data)

-- | generic hybrid symbols

data HSymbol sym =  BaseSymb sym
                  | HSymb Id HKind
   deriving (Show, Eq, Ord, Typeable, Data)

data HKind = Mod Int | Nom
   deriving (Show, Eq, Ord, Typeable, Data)

-- | generic raw symbols

data HRawSymbol sym raw_sym =
                         BaseRawSymbol raw_sym -- in the next two alternatives, only modalities and nominals 
                         | ASymbol (HSymbol sym) 
                         | AKindedSymb GKind Id
                 deriving (Show, Eq, Ord, Typeable, Data)

data GKind = Implicit -- it seems to me we never need this, we can rely on base logic for this! 
           | HKindAsG HKind
  deriving (Show, Eq, Ord, Typeable, Data)

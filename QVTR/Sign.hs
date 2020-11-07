{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./QVTR/Sign.hs
Description :  QVTR signature and sentences
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module QVTR.Sign where

import QVTR.As
import QVTR.Print ()

import qualified CSMOF.Sign as CSMOF
import CSMOF.Print ()

import Common.Doc
import Common.DocUtils
import Common.Id

import Data.Data
import qualified Data.HashMap.Strict as Map

import GHC.Generics (Generic)
import Data.Hashable


data RuleDef = RuleDef { name :: String
                       , top :: Bool
                       , parameters :: [CSMOF.TypeClass]
                       } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RuleDef

instance Pretty RuleDef where
  pretty (RuleDef nam to pars) =
    let t = text $ if to
            then "top relation"
            else "relation"
    in t <+> text nam <> lparen
    <> foldr ((<+>) . pretty) empty pars
    <> rparen


data Sign = Sign { sourceSign :: CSMOF.Sign
                 , targetSign :: CSMOF.Sign
                 , nonTopRelations :: Map.HashMap String RuleDef
                 , topRelations :: Map.HashMap String RuleDef
                 , keyDefs :: [(String, String)]
                 } deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange Sign where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty Sign where
  pretty (Sign souS tarS nonRel topRel keyD) =
    text "-- Source Metamodel"
    $++$
    pretty souS
    $++$
    text "-- Target Metamodel"
    $++$
    pretty tarS
    $++$
    text "-- Model Transformation"
    $++$
    text "Definition of Relations"
    $+$
    Map.foldr (($+$) . pretty) empty topRel
    $+$
    Map.foldr (($+$) . pretty) empty nonRel
    $++$
    text "Definition of Keys"
    $+$
    foldr (($+$) . pretty) empty keyD

emptySign :: Sign
emptySign = Sign { sourceSign = CSMOF.emptySign
                 , targetSign = CSMOF.emptySign
                 , nonTopRelations = Map.empty
                 , topRelations = Map.empty
                 , keyDefs = []
                 }


data Sen = KeyConstr { keyConst :: Key }
         | QVTSen { rule :: RelationSen }
         deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Sen

instance GetRange Sen where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty Sen where
  pretty (KeyConstr con) = pretty con
  pretty (QVTSen rel) = pretty rel


data RelationSen = RelationSen { ruleDef :: RuleDef
                               , varSet :: [RelVar]
                               , parSet :: [RelVar]
                               , sourcePattern :: Pattern
                               , targetPattern :: Pattern
                               , whenClause :: Maybe WhenWhere
                               , whereClause :: Maybe WhenWhere
                               } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RelationSen

instance GetRange RelationSen where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty RelationSen where
  pretty (RelationSen rD vS pS souP tarP whenC whereC) =
    pretty rD
    $++$
    text "Variables" <> colon <+> foldr ((<+>) . pretty) empty vS
    $++$
    text "Parameters" <> colon <+> foldr ((<+>) . pretty) empty pS
    $++$
    pretty souP
    $++$
    pretty tarP
    $++$
    (case whenC of
      Nothing -> text "When" <+> lbrace $+$ rbrace
      Just w -> text "When" <+> lbrace $+$ pretty w $+$ rbrace)
    $++$
    (case whereC of
      Nothing -> text "Where" <+> lbrace $+$ rbrace
      Just w -> text "Where" <+> lbrace $+$ pretty w $+$ rbrace)


data Pattern = Pattern { patVarSet :: [RelVar]
                       , patRels :: [(CSMOF.PropertyT, RelVar, RelVar)]
                       , patPreds :: [(String, String, OCL)]
                       } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Pattern

instance GetRange Pattern where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty Pattern where
  pretty (Pattern patVS patRel patPre) =
    text "Pattern" <+> lbrace
    $+$
    space <+> space <+> text "Variables" <> colon <+> foldr ((<+>) . pretty) empty patVS
    $+$
    space <+> space <+> text "Relations" <> colon <+> foldr (($+$) . pretty) empty patRel
    $+$
    space <+> space <+> text "Predicates" <> colon <+> foldr (($+$) . pretty) empty patPre
    $+$
    rbrace

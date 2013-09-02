{- |
Module      :  $Header$
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

import qualified Data.Map as Map


data RuleDef = RuleDef { name :: String
                       , top :: Bool
                       , parameters :: [CSMOF.TypeClass]
                       } deriving (Show, Eq, Ord)

instance Pretty RuleDef where
  pretty (RuleDef nam to pars) = 
    let t = case to of
              True -> text "top relation"
              False -> text "relation"
    in t <+> text nam <> lparen 
    <> foldr ((<+>) . pretty) empty pars
    <> rparen


data Sign = Sign { sourceSign :: CSMOF.Sign
                 , targetSign :: CSMOF.Sign
                 , nonTopRelations :: Map.Map String RuleDef
                 , topRelations :: Map.Map String RuleDef
                 , keyDefs :: [(String,String)]
                 } deriving (Show, Eq, Ord)

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
    Map.fold (($+$) . pretty) empty topRel
    $+$
    Map.fold (($+$) . pretty) empty nonRel
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
         | QVTSen { rules :: [Relation] } 
         deriving (Show, Eq, Ord)

instance GetRange Sen where
  getRange _ = nullRange
  rangeSpan _ = []      

instance Pretty Sen where
  pretty (KeyConstr con) = pretty con
  pretty (QVTSen tran) = pretty tran



{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable
  , GeneralizedNewtypeDeriving, TypeSynonymInstances, DeriveGeneric #-}
{- |
Module      :  ./FreeCAD/Logic_FreeCAD.hs
Description :  Instance of class Logic for FreeCAD
Copyright   :  (c) Christian Maeder DFKI, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

instance of class Logic for FreeCAD

-}

module FreeCAD.Logic_FreeCAD where

import Logic.Logic

import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.IRI (simpleIdToIRI)
import Common.LibName
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result

import ATerm.Lib

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import Data.Typeable

import FreeCAD.As
import FreeCAD.ATC_FreeCAD ()
import FreeCAD.PrintAs ()
import FreeCAD.Translator (processFile)

import Logic.Grothendieck (G_basic_spec (..))
import Syntax.AS_Library (fromBasicSpec, LIB_DEFN)
import GHC.Generics (Generic)
import Data.Hashable

data FreeCAD = FreeCAD deriving (Show, Generic)

instance Hashable FreeCAD

instance Language FreeCAD where
  description _ = "FreeCAD object representation language"

instance Pretty Text where
  pretty (Text s) = text s

newtype Text = Text { fromText :: String }
  deriving (Show, Eq, Ord, GetRange, Typeable, ShATermConvertible)

type FCMorphism = DefaultMorphism Sign

-- use generic Category instance from Logic.Logic

instance Syntax FreeCAD Document () () () where
  parse_basic_spec FreeCAD = Nothing

instance Sentences FreeCAD () Sign FCMorphism () where
  map_sen FreeCAD _ = return
  sym_of FreeCAD _ = [Set.singleton ()]
  symmap_of FreeCAD _ = Map.empty
  sym_name FreeCAD _ = genName "FreeCAD"

instance StaticAnalysis FreeCAD Document () () () Sign FCMorphism () ()
  where
  basic_analysis FreeCAD = Just basicFCAnalysis
  empty_signature FreeCAD = Sign { objects = Set.empty }
  is_subsig FreeCAD s1 s2 = Set.isSubsetOf (objects s1) $ objects s2

instance Logic FreeCAD
    ()                        -- Sublogics
    Document                  -- basic_spec
    ()                        -- no sentences
    ()                        -- no symb_items
    ()                        -- no symb_map_items
    Sign                      -- sign
    (DefaultMorphism Sign)    -- morphism
    ()                        -- no symbol
    ()                        -- no raw_symbol
    ()                        -- no proof_tree
    where
      stability FreeCAD = Experimental

readFreeCADLib :: FilePath -> LibName -> IO LIB_DEFN
readFreeCADLib fp ln = do
  bs <- processFile fp
  let sn = simpleIdToIRI $ mkSimpleId "FreeCAD-Design"
  return $ fromBasicSpec ln sn $ G_basic_spec FreeCAD bs

basicFCAnalysis :: (Document, Sign, GlobalAnnos)
                -> Result (Document, ExtSign Sign (), [Named ()])
basicFCAnalysis (bs, _, _) = return (bs, mkExtSign $ bsToSign bs, [])

bsToSign :: Document -> Sign
bsToSign doc = Sign $ Set.fromList doc

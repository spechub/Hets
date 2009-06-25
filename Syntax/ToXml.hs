{- |
Module      :  $Header$
Description :  xml output of Hets specification libaries
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml printing of Hets specification libaries
-}

module Syntax.ToXml
    (
      XmlPrintable
    , printLibDefnXml
    ) where

import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Print_AS_Structured

import Common.AS_Annotation
import Common.DocUtils

import Text.XML.Light

-- one can add global annos if necessary
printLibDefnXml :: LIB_DEFN -> String
printLibDefnXml ld = case toXml ld of (Elem e) -> ppTopElement e
                                      c -> ppContent c


-- if necessary replace Content by a custom data type

{- |
  this class defines the interface for writing XML
-}
class XmlPrintable a where
  -- | render instance to an XML Element
  toXml :: a -> Content

instance XmlPrintable LIB_DEFN where
    toXml (Lib_defn n il _ _) = mkEl "LIBDEFN" [] $ map (toXml . item) il
--    where toXml (Lib_defn aa ab _ ad) = 

instance XmlPrintable LIB_ITEM where
--    toXml (Spec_defn si (Genericity aa@(Params pl) ab@(Imported il) _) ac' _) =
    toXml (Spec_defn n _ as rg) =
        mkEl
        "LIB_ITEM"
        ["type", "SPEC", "name", toString n, "range", show rg]
        [toXml as]
    toXml x = mkComment $ take 15 (show x)  ++ "- not Supported"

instance XmlPrintable (Annoted SPEC) where
    toXml (Annoted s toprg la ra) =
        case s of
          Basic_spec bs rg -> mkEl "Basic" ["range", show rg] [toText bs]
          EmptySpec _ -> mkPEl "EmptySpec" []
          Translation as renam -> mkPEl "Translation" [toXml as, toText renam]
          Reduction as restr -> mkPEl "Reduction" [toXml as, toText restr]
          Union asl rg -> mkEl "Union" ["range", show rg] $ map toXml asl
          Extension asl rg -> mkEl "Extension" ["range", show rg] $ map toXml asl
          Free_spec as rg -> mkEl "Free" ["range", show rg] [toXml as]
          Cofree_spec as rg -> mkEl "Cofree" ["range", show rg] [toXml as]
          Local_spec as ins rg -> mkEl "Local" ["range", show rg] [toXml as, toXml ins]
          Closed_spec as rg -> mkEl "Closed" ["range", show rg] [toXml as]
          Group as rg -> mkEl "Group" ["range", show rg] [toXml as]
          Spec_inst n fargs rg -> mkEl "Inst" ["name", toString n, "range", show rg] $ map toXml fargs
          Qualified_spec ln as rg -> mkEl "Qualified" ["logic", toString ln, "range", show rg] [toXml as]
          Data _ _ s1 s2 _ -> mkComment "DATA not supported"

instance XmlPrintable (Annoted FIT_ARG) where
    toXml (Annoted farg toprg la ra) =
        case farg of
          Fit_spec as _ rg ->  mkEl "Fitspec" ["range", show rg] [toXml as]
          Fit_view n fargs rg -> mkEl "Fitview" ["name", toString n, "range", show rg] $ map toXml fargs


withNewLine :: String -> String
withNewLine s = "\n" ++ s ++ "\n"

toString :: Pretty a => a -> String
toString = show . pretty

toComment :: Pretty a => a -> Content
toComment = mkComment . toString

toText :: Pretty a => a -> Content
toText = mkText . toString

toVerb :: Pretty a => a -> Content
toVerb = mkVerb . toString

mkComment :: String -> Content
mkComment s = Text $ CData CDataRaw ("<!-- \n" ++ s ++ "\n -->") Nothing

mkText :: String -> Content
mkText s = Text $ CData CDataText s $ Just 30

mkVerb :: String -> Content
mkVerb s = Text $ CData CDataVerbatim s $ Just 50

-- make final element (no children)
mkFEl :: String -> [String] -> Content
mkFEl n a = mkEl n a []

-- make element
mkEl :: String -> [String] -> [Content] -> Content
mkEl n a c = Elem $ node (unqual n) (mkAtts a, c)

-- make pure element (no attributes)
mkPEl :: String -> [Content] -> Content
mkPEl n c = mkEl n [] c

mkAtts :: [String] -> [Attr]
mkAtts (x:y:l) = (Attr (unqual x) $ y) : mkAtts l
mkAtts _ = []

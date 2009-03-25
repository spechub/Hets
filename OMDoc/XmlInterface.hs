{-# LANGUAGE
  FlexibleInstances
  , TypeSynonymInstances
 #-}

{- |
Module      :  $Header$
Description :  OMDoc-to/from-XML conversion
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

The transformation of the OMDoc intermediate representation to and from XML.
-}



module OMDoc.XmlInterface
    ( XmlRepresentable
    , toXml
    , listToXml
    , listFromXml
    , makeComment
    , xmlOut
    ) where

import OMDoc.DataTypes
import Text.XML.Light
import Data.Maybe

-- | The implemented OMDoc version
omdoc_current_version :: String
omdoc_current_version = "1.2"

-- | often used element names
el_omdoc, el_theory, el_view, el_axiom, el_theorem, el_symbol, el_import
 , el_type, el_fmp, el_omobj, el_ombind, el_oms, el_ombvar, el_omattr
 , el_omatp, el_omv, el_oma, el_adt, el_sortdef, el_constructor
 , el_argument, el_insort, el_selector, el_requation, el_morphism :: QName

el_omdoc = (blank_name { qName = "omdoc" })
el_theory = (blank_name { qName = "theory" })
-- has perhaps to be renamed to view, depends on the omdoc version
el_view = (blank_name { qName = "theory-inclusion" })
el_axiom = (blank_name { qName = "axiom" })
el_theorem = (blank_name { qName = "theorem" })
el_symbol = (blank_name { qName = "symbol" })
el_import = (blank_name { qName = "import" })
el_type = (blank_name { qName = "type" })
el_fmp = (blank_name { qName = "FMP" })
el_omobj = (blank_name { qName = "OMOBJ" })
el_ombind = (blank_name { qName = "OMBIND" })
el_oms = (blank_name { qName = "OMS" })
el_ombvar = (blank_name { qName = "OMBVAR" })
el_omattr = (blank_name { qName = "OMATTR" })
el_omatp = (blank_name { qName = "OMATP" })
el_omv = (blank_name { qName = "OMV" })
el_oma = (blank_name { qName = "OMA" })

el_adt = (blank_name { qName = "adt" })
el_sortdef = (blank_name { qName = "sortdef" })
el_constructor = (blank_name { qName = "constructor" })
el_argument = (blank_name { qName = "argument" })
el_insort = (blank_name { qName = "insort" })
el_selector = (blank_name { qName = "selector" })
el_requation = (blank_name { qName = "requation" })
el_morphism = (blank_name { qName = "morphism" })

el_axiom_or_theorem :: Bool -> QName
el_axiom_or_theorem True = el_axiom
el_axiom_or_theorem False = el_theorem

-- | often used attribute names
at_id, at_version, at_cd, at_name, at_role, at_type, at_total, at_for
 , at_from, at_to :: QName

at_id = (blank_name { qName = "id", qPrefix = Just "xml" })
at_version = (blank_name { qName = "version" })
at_cd = (blank_name { qName = "cd" })
at_name = (blank_name { qName = "name" })
at_role = (blank_name { qName = "role" })
at_type = (blank_name { qName = "type" })
at_total = (blank_name { qName = "total" })
at_for = (blank_name { qName = "for" })
at_from = (blank_name { qName = "from" })
at_to = (blank_name { qName = "to" })


{- |
  this class defines the interface to read from and write to XML
-}
class XmlRepresentable a where
  -- | render instance to an XML Element
  toXml :: a -> Content
  -- | read instance from an XML Element
  fromXml :: Element -> Maybe a


xmlOut :: XmlRepresentable a => a -> String
xmlOut obj = case toXml obj of (Elem e) -> ppTopElement e
                               c -> ppContent c


listToXml :: XmlRepresentable a => [a] -> [Content]
listToXml l = map toXml l

listFromXml :: XmlRepresentable a => [Content] -> [a]
listFromXml elms = catMaybes $ map fromXml (onlyElems elms)

makeComment :: String -> Content
makeComment s = Text $ CData CDataRaw ("<!-- " ++ s ++ " -->") Nothing

typeToXml :: OMElement -> Content
typeToXml t = Elem $ Element el_type []
              [Elem $ Element el_omobj [] [toXml t] Nothing]
              Nothing

requationToXml :: (OMElement, OMElement) -> Content
requationToXml (from, to) =
    Elem $ Element el_requation []
             [Elem $ Element el_omobj [] [toXml from] Nothing,
              Elem $ Element el_omobj [] [toXml to] Nothing]
    Nothing

-- | The root instance for representing OMDoc in XML
instance XmlRepresentable OMDoc where
    toXml (OMDoc oid elms) =
        (Elem $ Element el_omdoc
         [Attr at_version omdoc_current_version, Attr at_id oid]
         (listToXml elms)
         Nothing)
    fromXml (Element n _ _ _)
        | n == el_omdoc =
            Nothing
        | otherwise = Nothing


-- | toplevel OMDoc elements to XML and back
instance XmlRepresentable TLElement where
    toXml (TLTheory tid elms) =
        (Elem $ Element el_theory
         [Attr at_id tid]
         (listToXml elms)
         Nothing)
    toXml (TLView (CD cdFrom _) (CD cdTo _) mor) =
        (Elem $ Element el_view
         [Attr at_from $ cdFrom, Attr at_to $ cdTo]
         [toXml mor]
         Nothing)
    fromXml (Element n _ _ _)
        | n == el_theory =
            Nothing
        | n == el_view =
            Nothing
        | otherwise = Nothing


-- | theory constitutive OMDoc elements to XML and back
instance XmlRepresentable TCElement where
    toXml (TCAxiomOrTheorem b sid obj) =
        Elem $ Element (el_axiom_or_theorem b) [Attr at_id sid]
         [Elem $ Element el_fmp []
          [Elem $ Element el_omobj []
            [toXml obj]
            Nothing]
          Nothing]
         Nothing
    toXml (TCSymbol sid symtype role) =
        Elem $ Element el_symbol
         [Attr at_name sid, Attr at_role (show role)]
         (case symtype of Nothing -> []
                          Just st -> [typeToXml st])
         Nothing
    toXml (TCADT sds) = (Elem $ Element el_adt [] (listToXml sds) Nothing)
    toXml (TCComment c) = (makeComment c)
    toXml (TCImport (CD c cdb) mor) =
        Elem $ Element el_import
         [Attr at_from $ c] -- ++ (show cdb)]
         [toXml mor]
         Nothing
    toXml (TCMorphism mapping) =
        Elem $ Element el_morphism
         []
         (map requationToXml mapping)
         Nothing
    fromXml (Element n _ _ _)
        | n == el_axiom =
            Nothing
        | n == el_theorem =
            Nothing
        | n == el_symbol =
            Nothing
        | n == el_import =
            Nothing
        | otherwise = Nothing


-- | OMDoc - Algebraic Data Types
instance XmlRepresentable OmdADT where
    toXml (ADTSortDef n b cs) =
        Elem $ Element el_sortdef
                 [Attr at_name n,
                  Attr at_type $ if b then "free" else "generated"]
                 (listToXml cs) Nothing
    toXml (ADTConstr n args) =
        Elem $ Element el_constructor [Attr at_name n] (listToXml args) Nothing
    toXml (ADTArg t sel) =
        Elem $ Element el_argument []
                 (typeToXml t :
                  case sel of Nothing -> []
                              Just s -> [toXml s])
                 Nothing
    toXml (ADTSelector n total) =
        Elem $ Element el_selector
                 [Attr at_name n,
                  Attr at_total $ if total then "yes" else "no"]
                 [] Nothing
    toXml (ADTInsort n) = Elem $ Element el_insort [Attr at_for n] [] Nothing
    fromXml _ = Nothing


-- | OpenMath elements to XML and back
instance XmlRepresentable OMElement where
    toXml (OMS d n) = Elem $ Element el_oms
                       [Attr at_cd (cd d), Attr at_name (name n)]
                       []
                       Nothing
    toXml (OMV n) = Elem $ Element el_omv [Attr at_name (name n)] [] Nothing
    toXml (OMATTT elm attr) =
        Elem $ Element el_omattr
         []
         [toXml attr, toXml elm]
         Nothing
    toXml (OMA args) = Elem $ Element el_oma [] (listToXml args) Nothing
    toXml (OMBIND symb vars body) =
        Elem $ Element el_ombind
         []
         [toXml symb,
          Elem (Element el_ombvar [] (listToXml vars) Nothing),
          toXml body]
         Nothing

    fromXml (Element n _ _ _)
        | n == el_axiom =
            Nothing
        | n == el_theorem =
            Nothing
        | n == el_symbol =
            Nothing
        | n == el_import =
            Nothing
        | otherwise = Nothing

-- | Helper instance for OpenMath attributes
instance XmlRepresentable OMAttribute where
    toXml (OMAttr e1 e2) =
        (Elem $ Element el_omatp
         []
         [toXml e1,
          toXml e2]
         Nothing)
    fromXml (Element _ _ _ _) = Nothing



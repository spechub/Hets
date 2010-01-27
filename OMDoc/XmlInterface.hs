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
    ( XmlRepresentable(toXml)
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
omdoc_current_version = "1.6"

-- | often used element names
el_omdoc, el_theory, el_view, el_structure
 , el_type, el_omobj, el_ombind, el_oms, el_ombvar, el_omattr
 , el_omatp, el_omv, el_oma, el_adt, el_sortdef, el_constructor
 , el_argument, el_insort, el_selector, el_morphism, el_conass
 , el_constant, el_definition :: QName

el_omdoc = (blank_name { qName = "omdoc" })
el_theory = (blank_name { qName = "theory" })
el_view = (blank_name { qName = "view" })
el_constant = (blank_name { qName = "constant" })
el_definition = (blank_name { qName = "definition" })
el_structure = (blank_name { qName = "structure" })
el_type = (blank_name { qName = "type" })
el_omobj = (blank_name { qName = "OMOBJ" })

el_ombind = (blank_name { qName = "OMBIND" , qPrefix = Just "om" })
el_oms = (blank_name { qName = "OMS" , qPrefix = Just "om" })
el_ombvar = (blank_name { qName = "OMBVAR" , qPrefix = Just "om" })
el_omattr = (blank_name { qName = "OMATTR" , qPrefix = Just "om" })
el_omatp = (blank_name { qName = "OMATP" , qPrefix = Just "om" })
el_omv = (blank_name { qName = "OMV" , qPrefix = Just "om" })
el_oma = (blank_name { qName = "OMA" , qPrefix = Just "om" })

el_adt = (blank_name { qName = "adt" })
el_sortdef = (blank_name { qName = "sortdef" })
el_constructor = (blank_name { qName = "constructor" })
el_argument = (blank_name { qName = "argument" })
el_insort = (blank_name { qName = "insort" })
el_selector = (blank_name { qName = "selector" })

el_morphism = (blank_name { qName = "morphism" })
el_conass = (blank_name { qName = "conass" })

-- | often used attribute names
at_version, at_cd, at_name, at_meta, at_role, at_type, at_total, at_for
 , at_from, at_to, at_base :: QName

-- at_id = (blank_name { qName = "id", qPrefix = Just "xml" })
at_version = (blank_name { qName = "version" })
at_cd = (blank_name { qName = "cd" })
at_name = (blank_name { qName = "name" })
at_meta = (blank_name { qName = "meta" })
at_role = (blank_name { qName = "role" })
at_type = (blank_name { qName = "type" })
at_total = (blank_name { qName = "total" })
at_for = (blank_name { qName = "for" })
at_from = (blank_name { qName = "from" })
at_to = (blank_name { qName = "to" })
at_base = (blank_name { qName = "cdbase" })

attr_om :: Attr
attr_om = Attr (blank_name { qName = "om" , qPrefix = Just "xmlns" })
          "http://www.openmath.org/OpenMath"

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
listFromXml elms = mapMaybe fromXml (onlyElems elms)

makeComment :: String -> Content
makeComment s = Text $ CData CDataRaw ("<!-- " ++ s ++ " -->") Nothing

typeToXml :: OMElement -> Content
typeToXml t = inContent el_type $ toOmobj $ toXml t

assignmentToXml :: (OMName, OMElement) -> Content
assignmentToXml (OMName from, to) =
    inAContent el_conass [Attr at_name from] $ toOmobj $ toXml to

constantToXml :: String -> String -> OMElement -> Maybe OMElement -> Content
constantToXml n r tp prf = 
    Elem $ Element el_constant
             [Attr at_name n, Attr at_role r]
             ([typeToXml tp]
              ++ map (inContent el_definition . toOmobj . toXml) (maybeToList prf))
             Nothing

inAContent :: QName -> [Attr] -> Content -> Content
inAContent qn a c = Elem $ Element qn a [c] Nothing

inContent :: QName -> Content -> Content
inContent qn c = inAContent qn [] c

toOmobj :: Content -> Content
toOmobj c = inAContent el_omobj [attr_om] c

-- don't need it now
--uriEncodeOMS :: OMCD -> OMName -> String
--uriEncodeOMS omcd (OMName omname) = uriEncodeCD omcd ++ "?" ++ omname

uriEncodeCD :: OMCD -> String
uriEncodeCD (CD omcd base) = (maybe "" id base) ++ "?" ++ omcd

tripleEncodeOMS :: OMCD -> OMName -> [Attr]
tripleEncodeOMS omcd (OMName omname)
    = pairEncodeCD omcd ++ [Attr at_name omname]

pairEncodeCD :: OMCD -> [Attr]
pairEncodeCD (CD omcd base) =
    (maybe [] (\x -> [Attr at_base x]) base) ++ [Attr at_cd omcd]


-- | The root instance for representing OMDoc in XML
instance XmlRepresentable OMDoc where
    toXml (OMDoc omname elms) =
        (Elem $ Element el_omdoc
         [Attr at_version omdoc_current_version, Attr at_name omname]
         (listToXml elms)
         Nothing)
    fromXml (Element n _ _ _)
        | n == el_omdoc =
            Nothing
        | otherwise = Nothing


-- | toplevel OMDoc elements to XML and back
instance XmlRepresentable TLElement where
    toXml (TLTheory tname meta elms) =
        (Elem $ Element el_theory
         ((Attr at_name tname)
           : case meta of Nothing -> []
                          Just mtcd -> [Attr at_meta $ uriEncodeCD mtcd])
         (listToXml elms)
         Nothing)
    toXml (TLView nm from to mor) =
        inAContent
        el_view [Attr at_name nm, Attr at_from $ uriEncodeCD from,
                      Attr at_to $ uriEncodeCD to]
                    $ toXml mor
    fromXml (Element n _ _ _)
        | n == el_theory =
            Nothing
        | n == el_view =
            Nothing
        | otherwise = Nothing


-- | theory constitutive OMDoc elements to XML and back
instance XmlRepresentable TCElement where
    toXml (TCAxiomOrTheorem mProof sname obj) =
        constantToXml
        sname (maybe "axiom" (const "theorem") mProof) obj mProof
    toXml (TCSymbol sname symtype role) =
        constantToXml sname (show role) symtype Nothing
    toXml (TCADT sds) = (Elem $ Element el_adt [] (listToXml sds) Nothing)
    toXml (TCComment c) = (makeComment c)
    toXml (TCImport nm from mor) =
        inAContent
        el_structure
        [Attr at_name nm, Attr at_from $ uriEncodeCD from] $ toXml mor
    toXml (TCMorphism mapping) =
        Elem $ Element el_morphism
         []
         (map assignmentToXml mapping)
         Nothing
    fromXml (Element n _ _ _)
        | n == el_constant =
            Nothing
        | n == el_structure =
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
                       (tripleEncodeOMS d n)
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
        | n == el_constant =
            Nothing
        | n == el_structure =
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



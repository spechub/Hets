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
import Data.List

-- | The implemented OMDoc version
omdoc_current_version :: String
omdoc_current_version = "1.6"

{-
-- the often used element names can be produced with this program

import Data.List
import Data.Char

val1 prfix f qual s = prfix ++ s ++ " = (blank_name { qName = " ++ show (f s) ++ qual ++ " })"
val2 prfix f qual s = prfix ++ s ++ " = toQN" ++ qual ++ " " ++ show (f s)

out = putStrLn out1
out1 = 
    let om1 = " , qPrefix = Just \"om\""
        om2 = "OM"
        om = om2
        val = val2
        elprfix = "el_"
        atprfix = "at_"
        toUpper = map Data.Char.toUpper
        typedecl prfix l = (Data.List.intercalate ", " $ map (\x -> prfix ++ x) l) ++ " :: QName"
        e1 = ["omdoc", "theory", "view", "structure", "type", "adt", "sortdef", "constructor", "argument", "insort", "selector", "morphism", "conass", "constant", "definition"]
        e2 = ["omobj"]
        e3 = ["ombind", "oms", "ombvar", "omattr", "omatp", "omv", "oma"]
        a1 = ["version", "cd", "name", "meta", "role", "type", "total", "for", "from", "to", "cdbase"]
    in unlines [ typedecl elprfix $ e1 ++ e2 ++ e3
               , ""
               , unlines $ map (val elprfix id "") e1
               , unlines $ map (val elprfix toUpper "") e2
               , unlines $ map (val elprfix toUpper om) e3
               , typedecl atprfix a1
               , ""
               , unlines $ map (val atprfix id "") a1]


-}

toQN :: String -> QName
toQN s = blank_name { qName = s }
toQNOM :: String -> QName
toQNOM s = blank_name { qName = s , qPrefix = Just "om" }

-- | often used element names

el_omdoc, el_theory, el_view, el_structure, el_type, el_adt
 , el_sortdef, el_constructor, el_argument, el_insort, el_selector
 , el_morphism, el_conass, el_constant, el_definition, el_omobj
 , el_ombind, el_oms, el_ombvar, el_omattr, el_omatp, el_omv, el_oma :: QName

el_omdoc = toQN "omdoc"
el_theory = toQN "theory"
el_view = toQN "view"
el_structure = toQN "structure"
el_type = toQN "type"
el_adt = toQN "adt"
el_sortdef = toQN "sortdef"
el_constructor = toQN "constructor"
el_argument = toQN "argument"
el_insort = toQN "insort"
el_selector = toQN "selector"
el_morphism = toQN "morphism"
el_conass = toQN "conass"
el_constant = toQN "constant"
el_definition = toQN "definition"

el_omobj = toQN "OMOBJ"

el_ombind = toQNOM "OMBIND"
el_oms = toQNOM "OMS"
el_ombvar = toQNOM "OMBVAR"
el_omattr = toQNOM "OMATTR"
el_omatp = toQNOM "OMATP"
el_omv = toQNOM "OMV"
el_oma = toQNOM "OMA"

at_version, at_cd, at_name, at_meta, at_role, at_type, at_total
 , at_for, at_from, at_to, at_cdbase :: QName

at_version = toQN "version"
at_cd = toQN "cd"
at_name = toQN "name"
at_meta = toQN "meta"
at_role = toQN "role"
at_type = toQN "type"
at_total = toQN "total"
at_for = toQN "for"
at_from = toQN "from"
at_to = toQN "to"
at_cdbase = toQN "cdbase"


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
assignmentToXml (from, to) =
    inAContent el_conass [Attr at_name $ encodeOMName from] $ toOmobj $ toXml to

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
--uriEncodeOMS omcd omname = uriEncodeCD omcd ++ "?" ++ encodeOMName omname

uriEncodeCD :: OMCD -> String
uriEncodeCD (CD omcd base) = (maybe "" id base) ++ "?" ++ omcd

encodeOMName :: OMName -> String
encodeOMName on = intercalate "/" (path on ++ [name on])

tripleEncodeOMS :: OMCD -> OMName -> [Attr]
tripleEncodeOMS omcd omname
    = pairEncodeCD omcd ++ [Attr at_name $ encodeOMName omname]

pairEncodeCD :: OMCD -> [Attr]
pairEncodeCD (CD omcd base) =
    (maybe [] (\x -> [Attr at_cdbase x]) base) ++ [Attr at_cd omcd]


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



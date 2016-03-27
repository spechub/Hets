{- |
Module      :  ./CSMOF/XMLKeywords.hs
Description :  keywords used for XML conversion
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.XMLKeywords where

import Text.XML.Light

metamodelK :: QName
metamodelK = QName {qName = "Metamodel", qURI = Just "urn:CSMOF.ecore", qPrefix = Just "CSMOF"}

metamodelNameK :: QName
metamodelNameK = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

modelK :: QName
modelK = QName {qName = "model", qURI = Nothing, qPrefix = Nothing}

modelNameK :: QName
modelNameK = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

elementK :: QName
elementK = QName {qName = "element", qURI = Nothing, qPrefix = Nothing}

elementNameK :: QName
elementNameK = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

elementTypeK :: QName
elementTypeK = QName {qName = "type", qURI = Just "http://www.w3.org/2001/XMLSchema-instance", qPrefix = Just "xsi"}

elementIsAbstractK :: QName
elementIsAbstractK = QName {qName = "isAbstract", qURI = Nothing, qPrefix = Nothing}

elementSuperClassK :: QName
elementSuperClassK = QName {qName = "superClass", qURI = Nothing, qPrefix = Nothing}

ownedAttributeK :: QName
ownedAttributeK = QName {qName = "ownedAttribute", qURI = Nothing, qPrefix = Nothing}

ownedAttributeLowerK :: QName
ownedAttributeLowerK = QName {qName = "lower", qURI = Nothing, qPrefix = Nothing}

ownedAttributeUpperK :: QName
ownedAttributeUpperK = QName {qName = "upper", qURI = Nothing, qPrefix = Nothing}

ownedAttributeNameK :: QName
ownedAttributeNameK = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

ownedAttributeTypeK :: QName
ownedAttributeTypeK = QName {qName = "type", qURI = Nothing, qPrefix = Nothing}

ownedAttributeOppositeK :: QName
ownedAttributeOppositeK = QName {qName = "opposite", qURI = Nothing, qPrefix = Nothing}

objectK :: QName
objectK = QName {qName = "object", qURI = Nothing, qPrefix = Nothing}

objectNameK :: QName
objectNameK = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

objectTypeK :: QName
objectTypeK = QName {qName = "type", qURI = Nothing, qPrefix = Nothing}

linkK :: QName
linkK = QName {qName = "link", qURI = Nothing, qPrefix = Nothing}

linkTypeK :: QName
linkTypeK = QName {qName = "type", qURI = Nothing, qPrefix = Nothing}

linkSourceK :: QName
linkSourceK = QName {qName = "source", qURI = Nothing, qPrefix = Nothing}

linkTargetK :: QName
linkTargetK = QName {qName = "target", qURI = Nothing, qPrefix = Nothing}

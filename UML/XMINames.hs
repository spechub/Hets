module UML.XMINames where

import           Text.XML.Light
import           UML.UML

xmiURI1 :: Maybe String
xmiURI2 :: Maybe String
--xmiURI1 = Just "http://www.eclipse.org/uml2/3.0.0/UML"
xmiURI1 = Just "http://www.eclipse.org/uml2/5.0.0/UML"
xmiURI2 = Just "http://www.omg.org/spec/XMI/20131001"
--xmiURI2 = Just "http://schema.omg.org/spec/XMI/2.1"

modelName :: Maybe String -> QName
modelName xmiURI1 = QName {qName = "Model", qURI = xmiURI1 , qPrefix = Just "uml"} -- uri:Just "http://www.eclipse.org/uml2/5.0.0/UML"

packagedElementName :: QName
packagedElementName = QName {qName = "packagedElement", qURI = Nothing, qPrefix = Nothing}

generalizationName :: QName
generalizationName = QName {qName = "generalization", qURI = Nothing, qPrefix = Nothing}

attributeName :: QName
attributeName = QName {qName = "ownedAttribute", qURI = Nothing, qPrefix = Nothing}

attrTypeName1 :: QName
attrTypeName1 = QName {qName = "type", qURI = Nothing, qPrefix = Nothing}

attrTypeName2 :: QName
attrTypeName2 = QName {qName = "href", qURI = Nothing, qPrefix = Nothing}

attrIdName :: Maybe String -> QName
attrIdName xmiURI2 = QName {qName = "id", qURI = xmiURI2 , qPrefix = Nothing}

typeName :: Maybe String -> QName
typeName xmiURI2 = QName {qName = "type", qURI = xmiURI2, qPrefix = Nothing}

nameName :: QName
nameName = QName {qName = "name", qURI = Nothing, qPrefix = Nothing}

attrGeneralName :: QName
attrGeneralName = QName {qName = "general", qURI = Nothing, qPrefix = Nothing}

procedureName :: QName
procedureName = QName {qName = "ownedOperation", qURI = Nothing, qPrefix = Nothing}

procParaName :: QName
procParaName = QName {qName = "ownedParameter", qURI = Nothing, qPrefix = Nothing}

procDirName :: QName
procDirName = QName {qName = "direction", qURI = Nothing, qPrefix = Nothing}

assoEndName :: QName
assoEndName = QName {qName = "memberEnd", qURI = Nothing, qPrefix = Nothing}

-- state machinge

smRegionName :: QName
smRegionName = QName {qName = "region", qURI = Nothing, qPrefix = Nothing}

smSubvertexName :: QName
smSubvertexName = QName {qName = "subvertex", qURI = Nothing, qPrefix = Nothing}

smStateName :: QName
smStateName = QName {qName = "state", qURI = Nothing, qPrefix = Nothing}

sName :: String -> QName
sName s = QName {qName = s, qURI = Nothing, qPrefix = Nothing}

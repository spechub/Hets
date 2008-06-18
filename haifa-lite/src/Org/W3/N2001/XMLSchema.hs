{-# OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances -cpp #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Org.W3.N2001.XMLSchema
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- An equivelant module for <http://www.w3.org/2001/XMLSchema> schema and the data-types therein.
-- This is just a shell right now, providing a small number of types and the namespace. This
-- should eventually provide all the data-types required to parse a Schema.
--
-- This is a work in progress. It certainly won't be able to parse any schema thrown at it
-- yet.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the
-- GNU General Public License as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not,
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Org.W3.N2001.XMLSchema ( Int, Long, String, Decimal, Float, Double, Boolean, Duration, HexBinary, AnyURI, QName, XSDType(..), Base64Binary(..)
                              , Element(..), ComplexType(..), Sequence(..), Group(..), Choice(..), ComplexContent(..)
                              , SimpleContent(..), All(..), Attribute(..), AttributeGroup(..), Schema(..), ComplexRestriction(..)
                              , ComplexExtension(..)
                              , simpleElement, simpleComplexType, Any
                              , deriveXSDType) where

import Control.Monad.State
import Data.Typeable
import qualified Data.Char
import Data.Char
import Network.URI
import qualified Text.XML.Serializer as GXS
import Text.XML.Serializer.Core
import Text.XML.Serializer.Derive
import Text.XML.Serializer.Datatypes hiding (Choice, Sequence)
import Text.XML.Serializer.Encoders
import Text.XML.HXT.Parser hiding (choice)
import Text.XML.HXT.Aliases
import Control.Monad
import Data.Generics2 hiding (ID)
import Data.Maybe
import Data.Int
import Data.Word
import Data.Dynamic
import System.Time
import qualified Codec.Binary.Base64 as Base64
import Numeric
import Data.DynamicMap

tns = parseURI "http://www.w3.org/2001/XMLSchema"
prefix = "xsd"

class XSDType a where
    xsdType :: a -> [String]
    xsdType _ = []

----------------------------------------------------------------------------------------------------------------
-- GROUND XSD TYPES
----------------------------------------------------------------------------------------------------------------

type NCName   = String
type ID       = String
type Decimal  = Prelude.Double
type Duration = System.Time.CalendarTime
type Boolean  = Bool
type Long     = Int64

-- This makes life easy, because most types already have the right names, they just need the first letter lowercase.
-- instance Typeable a => XSDType a where xsdType x = [(\x -> (toLower $ head x):tail x) $ show $ typeOf x]

#ifndef __HADDOCK__
-- Qualify ground types
$(qualifyP [''Bool, ''Int, ''Double, ''Int64, ''CalendarTime, ''Float, ''Integer
           , ''Int8, ''Int16, ''Word8, ''Word16, ''Word32, ''Word64] "http://www.w3.org/2001/XMLSchema" "xsd")

-- Have to derive this manually
instance XMLNamespace Char where
    namespaceURI _ = tns
    defaultPrefix _ = prefix

-- Instances where we need to do it explicitly
instance XSDType a => XSDType [a] where xsdType = concat . map xsdType
instance XSDType a => XSDType (Maybe a) where xsdType = xsdType . fromJust

-- Query type case for a String
instance XSDType String   where xsdType _ = ["string"]
instance XMLData Char

deriveXSDType t x = (deriveXTypeElem t x) { xmlMetaData = addToDM (QN prefix t (show $ fromJust tns)) xsdTypeKey emptyDM }

setXSDType (n, ns) x = x { xmlMetaData = addToDM (QN "" n ns) xsdTypeKey (xmlMetaData x) }
setXSDTypeE (n, ns) = [| setXSDTypeE (n, ns) |]

-- Signed numeric types

instance XSDType Int64    where xsdType _ = ["long"]
instance XMLData Long where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "long"
    xmlDecode = decodeViaRead

instance XSDType Int where xsdType _ = ["int"]
instance XMLData Int where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "int"
    xmlDecode = decodeViaRead

instance XSDType Int16 where xsdType _ = ["short"]
instance XMLData Int16 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "short"
    xmlDecode = decodeViaRead

instance XSDType Int8     where xsdType _ = ["byte"]
instance XMLData Int8 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "byte"
    xmlDecode = decodeViaRead

instance XSDType Integer   where xsdType _ = ["integer"]
instance XMLData Integer where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "integer"
    xmlDecode = decodeViaRead

-- Unsigned numeric types

instance XSDType Word64     where xsdType _ = ["unsignedLong"]
instance XMLData Word64 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "unsignedLong"
    xmlDecode = decodeViaRead

instance XSDType Word32     where xsdType _ = ["unsignedInt"]
instance XMLData Word32 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "unsignedInt"
    xmlDecode = decodeViaRead

instance XSDType Word16     where xsdType _ = ["unsignedShort"]
instance XMLData Word16 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "unsignedShort"
    xmlDecode = decodeViaRead

instance XSDType Word8     where xsdType _ = ["unsignedByte"]
instance XMLData Word8 where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "unsignedByte"
    xmlDecode = decodeViaRead

instance XSDType Float     where xsdType _ = ["float"]
instance XMLData Float where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "float"
    xmlDecode = decodeViaRead

instance XSDType Double     where xsdType _ = ["double"]
instance XMLData Double where
    xmlEncode = encodeViaShow
    toXMLType = deriveXSDType "double"
    xmlDecode = decodeViaRead

instance XSDType Bool     where xsdType _ = ["boolean"]
instance XMLData Bool where
    xmlEncode _ x = [SLeaf $ txt (if x then "true" else "false")]
    toXMLType   = deriveXSDType "boolean"
    xmlDecode     = readText >>= \x -> case x of
                                       "true"  -> return True
                                       "false" -> return False
                                       "1"     -> return True
                                       "0"     -> return False
                                       _       -> mzero


instance (XSDType a, XSDType b) => XSDType (Either a b) where xsdType x = either xsdType xsdType x

{-
instance Data ctx URI => XMLData ctx URI where xmlEncode _ uri = [[txt $ show uri]]

instance Data ctx String => XMLNamespace ctx String where
    defaultPrefix _ _ = prefix
    namespaceURI _ _ = tns

instance (XMLNamespace ctx a, XSDType ctx a) => ElementName ctx a where
    elementName ctx x = (head $ xsdType ctx x)
-}
{-
3.2.7 dateTime
3.2.8 time
-}
type Date     = System.Time.CalendarTime
{-
3.2.10 gYearMonth
3.2.11 gYear
3.2.12 gMonthDay
3.2.13 gDay
3.2.14 gMonth
-}

data HexBinary    = Hex{fromHex::Int} deriving (Show)
data Base64Binary = Base64{fromBase64::[Word8]} deriving Show
$(qualifyP [''HexBinary, ''URI, ''URIAuth, ''Base64Binary] "http://www.w3.org/2001/XMLSchema" "xsd")
$(derive [''HexBinary, ''Base64Binary])
$(deriveData [''URI, ''URIAuth])


instance XSDType HexBinary     where xsdType _ = ["hexBinary"]
instance XMLData HexBinary where
    xmlEncode  _ x = [SLeaf $ txt $ showHex (fromHex x) ""]
    toXMLType    = deriveXSDType "hexBinary"
    xmlDecode      = do x <- readText
                        return $ Hex $ read $ (++) "0x" x

type AnyURI = URI

instance XSDType URI where xsdType _ = ["anyURI"]
instance XMLData URIAuth
instance XMLData URI where
    xmlEncode   = encodeViaShow
    toXMLType = deriveXSDType "anyURI"
    xmlDecode = do x <- readText
                   maybe mzero return (parseURIReference x) -- I'm being lenient with what I class as a URI.

instance XSDType QName where xsdType _ = ["QName"]
instance XMLNamespace QName where
    namespaceURI _       = parseURI "http://www.w3.org/2001/XMLSchema"
    containsNamespaces (QN _ _ ns) = maybeToList (parseURIReference ns)
    defaultPrefix _      = "xsd"

instance XMLData QName where
    xmlEncode dm (QN _ l ns) = let nst = lookupDM_D nstIKey dm
                                   p   = maybe "" (\x->x++":") $ parseURIReference ns >>= \u -> lookup u nst in
                                   [SLeaf $ txt $ p++l]
    toXMLType = deriveXSDType "QName"
    xmlDecode = do s <- get
                   let nst = lookupDM_D nstKey $ dynMap s
                   x <- readText
                   let sp = span (/= ':') x
                   if (null $ snd sp) then return $ (QN "" (fst sp) "")
                                      else let p  = fst sp
                                               ns = fromMaybe "" (lookup p nst >>= return . show) in
                                               return $ (QN p (tail $ snd sp) ns)



instance XSDType Base64Binary where xsdType _ = ["base64Binary"]

instance XMLData Base64Binary where
    xmlEncode dm x = [SLeaf $ txt $ Base64.encode $ fromBase64 x]
    toXMLType    = deriveXSDType "base64Binary"
    -- FIXME: Base64's decode really should be done in a monad to make it safer.
    xmlDecode      = do
      t <- readText
      v <- maybe (fail "Base64.decode") return $ Base64.decode t
      return $ Base64 v

xsdTypes   = [(typeOf (undefined::Int)             , ["int"])
             ,(typeOf (undefined::String)          , ["string"])
             ,(typeOf (undefined::Float)           , ["float"])
             ,(typeOf (undefined::Double)          , ["double"])
             ,(typeOf (undefined::Long)            , ["long"])
             ,(typeOf (undefined::Short)           , ["short"])
             ,(typeOf (undefined::Byte)            , ["byte"])
             ,(typeOf (undefined::Bool)            , ["bool"])
             ,(typeOf (undefined::QName)           , ["QName"])
             ,(typeOf (undefined::URI)             , ["anyURI"])
             ,(typeOf (undefined::HexBinary)       , ["hexBinary"])
             ,(typeOf (undefined::Base64Binary)    , ["base64Binary"])
             ]

{-
3.2.19 NOTATION
-}

{-
3.3.1 normalizedString
3.3.2 token
3.3.3 language
3.3.4 NMTOKEN
3.3.5 NMTOKENS
3.3.6 Name
3.3.7 NCName
3.3.8 ID
3.3.9 IDREF
3.3.10 IDREFS
3.3.11 ENTITY
3.3.12 ENTITIES
3.3.13 integer
3.3.14 nonPositiveInteger
3.3.15 negativeInteger
3.3.16 long
3.3.17 int
3.3.18 short
3.3.19 byte
3.3.20 nonNegativeInteger
3.3.21 unsignedLong
3.3.22 unsignedInt
3.3.23 unsignedShort
3.3.24 unsignedByte
3.3.25 positiveInteger
-}

{-
   Although these are derived types, for now we simply set them as synoyms of their base type. This will remain
   if validation based on actual type is not required. (If validation is done on the unprocessed XML document
   itself, which is more likely). The other reason to make them individual types is if we required a one-one
   mapping between Haskell types and XSD types (which clearly isn't the case with this system). If we do have
   to create proper equivelant types, do using type renaming and init major type-classes (Eq, Ord, Num etc.) for
   each.
-}

type NormalizedString     = String
type Token                = NormalizedString
type Language             = Token

type NMTOKEN              = Token
type NMTOKENS             = [Token]
type Name                 = Token

type IDREF                = NCName
type IDREFS               = [IDREF]
type ENTITY               = NCName

type ENTITIES             = [ENTITY]


-- type Integer              = Int64
type NonPositiveInteger   = Integer
type NegativeInteger      = NonPositiveInteger
-- Long is above as Int64
-- Int  is above as Int
type Short                = Int16
type Byte                 = Int8
type NonNegativeInteger   = Word64
type UnsignedLong         = Word64
type UnsignedInt          = Word32
type UnsignedShort        = Word16
type UnsignedByte         = Word8
type PositiveInteger      = NonNegativeInteger


{-

<element
  abstract = boolean : false
  block = (#all | List of (extension | restriction | substitution))
  default = string
  final = (#all | List of (extension | restriction))
  fixed = string
  form = (qualified | unqualified)
  id = ID
  maxOccurs = (nonNegativeInteger | unbounded)  : 1
  minOccurs = nonNegativeInteger : 1
  name = NCName
  nillable = boolean : false
  ref = QName
  substitutionGroup = QName
  type = QName
  {any attributes with non-schema namespace . . .}>
  Content: (annotation?, ((simpleType | complexType)?, (unique | key | keyref)*))
</element>

-}



data ERS = Extension | Restriction | Substitution deriving Show
data AllOr a = A_All | A_Or a deriving Show

instance XMLNamespace a => XMLNamespace (AllOr a) where
    namespaceURI _ = namespaceURI (undefined::a)

data Qualification = Qualified | Unqualified deriving Show

data Annotation = Annotation deriving Show

data SimpleType  = SimpleType deriving Show
--data ComplexType = ComplexType deriving Show
data KeyType = KeyType deriving Show

type AllOrERS = AllOr ERS


$(derive [''UpperBound])
instance XMLData UpperBound where
    xmlEncode = encodeViaShow
    toXMLType = deriveXMLType
    xmlDecode = do x <- readText
                   if ((map toLower x)=="unbounded") then return $ Unbounded
                                                     else do i <- lift $ readM x
                                                             return (Bounded i)

-- Main XML Schema Types --------------------------------------------------------------------------------------------

data Schema = Schema { schema_types :: [ComplexType]
                     , schema_targetNamespace :: Maybe URI } deriving Show

emptySchema :: Schema
emptySchema = Schema [] Nothing

data Element = Element { -- Attributes
                         element_abstract          :: Maybe Bool
                       , element_block             :: Maybe String -- (AllOr ERS)
                       , element_default           :: Maybe String
                       , element_final             :: Maybe String -- (AllOr ERS)
                       , element_fixed             :: Maybe String
                       , element_form              :: Maybe String -- Qualification
                       , element_id                :: Maybe ID
                       , element_maxOccurs         :: Maybe UpperBound
                       , element_minOccurs         :: Maybe LowerBound
                       , element_name              :: NCName
                       , element_nillable          :: Maybe Bool
                       , element_ref               :: Maybe QName
                       , element_substitutionGroup :: Maybe QName
                       , element_type              :: Maybe QName
                         -- Elements
                       , element_annotation        :: Maybe Annotation
                       , element_innerType         :: Maybe (U2 SimpleType ComplexType)
                       , element_keyType           :: Maybe [KeyType]
                       } deriving Show

instance Cardinality Element where
    getCardinality e = (fromMaybe 1 (element_minOccurs e), fromMaybe (Bounded 1) (element_maxOccurs e))

simpleElement n t c = Element Nothing Nothing Nothing Nothing Nothing Nothing Nothing (Just $ maxOccurs c) (Just $ minOccurs c) n Nothing Nothing Nothing t Nothing Nothing Nothing

{-
<complexType
  abstract = boolean : false
  block = (#all | List of (extension | restriction))
  final = (#all | List of (extension | restriction))
  id = ID
  mixed = boolean : false
  name = NCName
  {any attributes with non-schema namespace . . .}>
  Content: (annotation?, (simpleContent | complexContent | ((group | all | choice | sequence)?, ((attribute | attributeGroup)*, anyAttribute?))))
</complexType>
-}


data ComplexType =
    ComplexType { ctype_abstract   :: Maybe Bool
                , ctype_block      :: Maybe String --(AllOr ERS)
                , ctype_final      :: Maybe String --(AllOr ERS)
                , ctype_id         :: Maybe ID
                , ctype_mixed      :: Maybe Boolean
                , ctype_name       :: Maybe NCName
                , ctype_annotation :: Maybe Annotation
                , ctype_content    :: U3 SimpleContent
                                         ComplexContent
                                         ((U4 Group All Choice Sequence)
                                         ,[U2 Attribute AttributeGroup])

                } deriving Show

simpleComplexType :: NCName -> U4 Group All Choice Sequence -> [U2 Attribute AttributeGroup] -> ComplexType
simpleComplexType n c a = ComplexType Nothing Nothing Nothing Nothing Nothing (Just n) Nothing (U33 (c,  a))

data Group = Group deriving Show


data All = All { all_id         :: Maybe ID
               , all_minOccurs  :: Maybe LowerBound
               , all_maxOccurs  :: Maybe UpperBound
               , all_annotation :: Maybe Annotation
               , all_content    :: [Element]
               } deriving Show


data Any = Any deriving Show
data Attribute = Attribute { attr_default    :: Maybe String
                           , attr_fixed      :: Maybe String
                           , attr_form       :: Maybe String -- Qualification
                           , attr_id         :: Maybe ID
                           , attr_name       :: Maybe NCName
                           , attr_ref        :: Maybe QName
                           , attr_type       :: Maybe QName
                           , attr_use        :: Maybe String -- Use
                           , attr_anyAttr    :: AttrSet
                           , attr_annotation :: Maybe Annotation
                           , attr_simpleType :: Maybe SimpleType
                           } deriving Show


data AttributeGroup = AttributeGroup deriving Show

data Sequence = Sequence { seq_minOccurs :: Maybe LowerBound
                         , seq_maxOccurs :: Maybe UpperBound
                         , seq_content   :: [U5 Element Group Choice Sequence Any]
                         } deriving Show

instance Cardinality Sequence where
    getCardinality e = (fromMaybe 1 (seq_minOccurs e), fromMaybe (Bounded 1) (seq_maxOccurs e))

data Choice = Choice { cho_minOccurs :: Maybe LowerBound
                     , cho_maxOccurs :: Maybe UpperBound
                     , cho_content   :: [U5 Element Group Choice Sequence Any]
                     } deriving Show

instance Cardinality Choice where
    getCardinality c = (fromMaybe 1 (cho_minOccurs c), fromMaybe (Bounded 1) (cho_maxOccurs c))

data SimpleContent = SimpleContent { scont_id         :: Maybe ID
                                   , scont_annotation :: Maybe Annotation
                                   , scont_content    :: U2 SimpleRestriction SimpleExtension
                                   } deriving Show

data SimpleRestriction = SimpleRestriction deriving Show
data SimpleExtension = SimpleExtension deriving Show


data ComplexContent = ComplexContent { ccont_id         :: Maybe ID
                                     , ccont_mixed      :: Maybe Boolean
                                     , ccont_annotation :: Maybe Annotation
                                     , ccont_content    :: U2 ComplexRestriction ComplexExtension
                                     } deriving Show

data ComplexRestriction =
    ComplexRestriction { cres_base       :: QName
                       , cres_id         :: Maybe ID
                       , cres_annotation :: Maybe Annotation
                       , cres_content    :: (Maybe (U4 Group All Choice Sequence)
                                            ,[U2 Attribute AttributeGroup]
                                            )
                       } deriving Show

data ComplexExtension =
    ComplexExtension { cext_base       :: QName
                     , cext_id         :: Maybe ID
                     , cext_annotation :: Maybe Annotation
                     , cext_content    :: (Maybe (U4 Group All Choice Sequence)
                                          ,[U2 Attribute AttributeGroup]
                                          )
                     } deriving Show

-- XML Schema Serializers ------------------------------------------------------------------------------------------------

-- Qualify all Schema elements.
$(qualifyP [ ''Element, ''Annotation, ''SimpleType, ''ComplexType
           , ''Qualification, ''ERS, ''KeyType, ''Group, ''All
           , ''Choice, ''Sequence, ''SimpleContent, ''ComplexContent
           , ''Any, ''Attribute, ''AttributeGroup, ''Schema
           , ''SimpleRestriction, ''SimpleExtension, ''ComplexRestriction
           , ''ComplexExtension] "http://www.w3.org/2001/XMLSchema" "xsd")

{-

$(derive [''Element, ''AllOr, ''ComplexType, ''Sequence, ''Group, ''Choice, ''SimpleType, ''Annotation, ''Schema, ''SimpleContent, ''ComplexContent, ''ComplexExtension, ''ComplexRestriction, ''Attribute, ''All])
$(xmlify [''Qualification, ''ERS, ''KeyType, ''Any, ''AttributeGroup, ''SimpleRestriction, ''SimpleExtension ] [])


instance XMLData Schema where
    toXMLType x =
        xmlType { fieldSchema   = fieldsQ [elmN occursAny "complexType", atr "targetNamespace"] tns
                  , defaultSchema = Just $ Elem occursOnce "schema" tns
                  , elementNames  = ["schema"]
                  , isInterleaved = True
                  }

instance XMLData Attribute where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ ((map atr ["default", "fixed", "form", "id", "name", "ref",
                                                     "type", "use"]) ++
                                                    [anyAtr AnyNS,
                                                     elmN occursMaybe "annotation",
                                                     elmN occursMaybe "simpleType"]) tns
                  , elementNames = ["attribute"]
                  }

instance XMLData SimpleContent where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ ([ atr "id"
                                           , elmN occursMaybe "annotation"
                                           , choiceN occursOnce [ elm "restriction"
                                                                , elm "extension" ]
                                           ]) tns
                  , elementNames = ["simpleContent"]
                  }

instance XMLData ComplexContent where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ ([ atr "id"
                                           , atr "mixed"
                                           , elmN occursMaybe "annotation"
                                           , choiceN occursOnce [ elm "restriction"
                                                                , elm "extension" ]
                                           ]) tns
                  , elementNames = ["complexContent"]
                  }

instance XMLData ComplexRestriction where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [ atr "base"
                                          , atr "id"
                                          , elmN occursMaybe "annotation"
                                          , seqx [choiceN occursMaybe [elm "group",
                                                                       elm "all",
                                                                       elm "choice",
                                                                       elm "sequence"
                                                                      ],
                                                  choiceN occursAny [elm "attribute",
                                                                     elm "attributeGroup"
                                                                    ]
                                                 ]
                                          ] tns
                  , elementNames = ["restriction"]
                  }

instance XMLData ComplexExtension where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [ atr "base"
                                          , atr "id"
                                          , elmN occursMaybe "annotation"
                                          , seqx [choiceN occursMaybe [elm "group",
                                                                       elm "all",
                                                                       elm "choice",
                                                                       elm "sequence"
                                                                      ],
                                                  choiceN occursAny [elm "attribute",
                                                                     elm "attributeGroup"
                                                                    ]
                                                 ]
                                          ] tns
                  , elementNames = ["extension"]
                  }

instance XMLData Annotation where
   xmlDecode = mzero

instance XMLData SimpleType where
   xmlDecode = mzero


instance (Data DictXMLData a, XMLNamespace a) => XMLData (AllOr a) where
    toXMLType = deriveXMLType

instance XMLData Element where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ ((map atr ["abstract", "block", "default", "final", "fixed", "form",
                                                   "id", "maxOccurs", "minOccurs", "name", "nillable", "ref",
                                                   "substitutionGroup", "type"]) ++
                                                  [elmN occursMaybe "annotation",
                                                   choiceN occursMaybe [elm "simpleType",
                                                                        elm "complexType"],
                                                   elmN occursMaybe "keyType"]) tns
                  , elementNames = ["element"]
                  , defaultValues = [ Just (toDyn (Just False)), Nothing, Nothing, Nothing, Nothing, Nothing, Nothing
                                    , Just (toDyn (Just (1::Int))), Just (toDyn (Just (1::Int))), Nothing, Just $ toDyn (Just False)]
                  }

instance XMLData ComplexType where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ ((map atr ["abstract", "block", "final", "id", "mixed", "name"]) ++
                                        [elmN occursMaybe "annotation",
                                         choice [elm "simpleContent",
                                                 elm "complexContent",
                                                 seqx [choice [elm "group",
                                                               elm "all",
                                                               elm "choice",
                                                               elm "sequence"
                                                              ],
                                                       choiceN occursAny [elm "attribute",
                                                                          elm "attributeGroup"
                                                                         ]
                                                      ]
                                                ]
                                        ]) tns
                  , elementNames = ["complexType"]
                  }



instance XMLData Sequence where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [atr "minOccurs",
                                         atr "maxOccurs",
                                         choiceN occursAny [elm "element",
                                                            elm "group",
                                                            elm "choice",
                                                            elm "sequence",
                                                            elm "any"
                                                           ]
                                        ] tns
                  , elementNames = ["sequence"]
                  }

instance XMLData All where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [atr "id",
                                           atr "minOccurs",
                                           atr "maxOccurs",
                                           elmN occursMaybe "annotation",
                                           elmN occursAny "element"
                                          ] tns
                  , elementNames = ["all"]
                  }

instance XMLData Choice where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [atr "minOccurs",
                                         atr "maxOccurs",
                                         choiceN occursAny [elm "element",
                                                            elm "group",
                                                            elm "choice",
                                                            elm "sequence",
                                                            elm "any"]
                                        ] tns
                  , elementNames = ["choice"]
                  }

instance XMLData Group where
    toXMLType x =
        xmlType { fieldSchema = fieldsQ [atr "minOccurs",
                                         atr "maxOccurs",
                                         choice [elm "element",
                                                 elm "group",
                                                 elm "choice",
                                                 elm "sequence",
                                                 elm "any"]] tns
                  , elementNames = ["group"]
                  }

instance XMLNamespace AttrSet
instance XMLData AttrSet where
    xmlDecode = do s <- get
                   case (particles s) of
                       (SLeaf (_, as):_) -> return $ AttrSet $ map (\t -> (qnameOf t, xshow $ getChildren t)) as
                       _                 -> return $ AttrSet []

    xmlEncode dm (AttrSet l) = [SNode (map (\(q,t) -> [SLeaf $ qattr q (txt t)]) l)]


instance XMLNamespace ElemSet
instance XMLData ElemSet where
    xmlDecode = do s <- get
                   case (particles s) of
                       (SLeaf (es, _):_) -> return $ ElemSet $ map (\t -> (qnameOf t, xshow $ getChildren t)) es
                       _                 -> return $ ElemSet []
    xmlEncode dm (ElemSet l) = [SNode (map (\(q,t) -> [SLeaf $ qetag q += (txt t)]) l)]
-}
#endif

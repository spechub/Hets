-- |
-- The core data types of HDOM.
-- This module is based on the module NTree which was adapted from
-- HaXml (<http://www.cs.york.ac.uk/fp/HaXml/>)
--
-- Version : $Id$

module Text.XML.HXT.DOM.XmlTreeTypes
    ( module Data.NTree
    , module Data.AssocList,

      -- * The XML Node Data Type
      XNode(..)
    , XmlTree
    , XmlTrees
    , XmlFilter
    , XmlSFilter,

      -- * The Data Types for the Document Type Definitions
      DTDElem(..)
    , TagName
    , AttrName
    , Attributes,

      -- * The Data Type and Access Functions for Namespace aware Names
      QName(..)
    , tName
    , aName
    , qualifiedName
    , universalName
    , mkName
    , mkNsName
    , mkPrefixLocalPart
    ,

      -- * Constants for Error Messages
      c_ok
    , c_warn            -- constants for error levels
    , c_err
    , c_fatal
    )

where

import Data.NTree
import Data.AssocList

-- -----------------------------------------------------------------------------
--
-- Basic types for xml tree and filters

-- | Node of xml tree representation

type XmlTree	= NTree    XNode

-- | List of nodes of xml tree representation

type XmlTrees	= NTrees   XNode

-- | A functions that takes a node and returns a list of nodes

type XmlFilter	= TFilter  XNode

-- | A function that takes a list of nodes and returns a list of nodes

type XmlSFilter	= TSFilter XNode


-- -----------------------------------------------------------------------------
--
-- XNode

-- | Represents elements

data XNode	= XText		String			-- ^ ordinary text	(leaf)
		| XCharRef	Int			-- ^ character reference	(leaf)
		| XEntityRef	String			-- ^ entity reference	(leaf)
		| XCmt		String			-- ^ comment		(leaf)
		| XCdata	String			-- ^ CDATA section	(leaf)
		| XPi		TagName XmlTrees	-- ^ Processing Instr	(leaf)
							--   with list of attributes.
							--   If tag name is xml, attributs are \"version\", \"encoding\", \"standalone\",
							--   else attribute list is empty, content is a text child node
		| XTag		TagName XmlTrees	-- ^ tag with list of attributes (inner node or leaf)
		| XDTD		DTDElem Attributes	-- ^ DTD element with assoc list for dtd element features
		| XAttr		AttrName		-- ^ attribute, attribute value is stored in children
		| XError	Int String		-- ^ error message with level and text
		  deriving (Eq, Ord, Show, Read)

-- -----------------------------------------------------------------------------
--
-- DTDElem

-- | Represents a DTD element

data DTDElem	= DOCTYPE	-- ^ attr: name, system, public	XDTD elems as children
		| ELEMENT	-- ^ attr: name, kind
		                --
				--  name: element name
		                --
				--  kind: \"EMPTY\" | \"ANY\" | \"\#PCDATA\" | children | mixed
		| CONTENT	-- ^ element content
		                --
				--  attr: kind, modifier
		                --
				--  modifier: \"\" | \"?\" | \"*\" | \"+\"
		                --
				--  kind: seq | choice
		| ATTLIST	-- ^ attributes:
		                --  name - name of element
		                --
				--  value - name of attribute
		                --
				--  type: \"CDATA\" | \"ID\" | \"IDREF\" | \"IDREFS\" | \"ENTITY\" | \"ENTITIES\" |
		                --
				--        \"NMTOKEN\" | \"NMTOKENS\" |\"NOTATION\" | \"ENUMTYPE\"
		                --
				--  kind: \"#REQUIRED\" | \"#IMPLIED\" | \"DEFAULT\"
		| ENTITY	-- ^ for entity declarations
		| PENTITY	-- ^ for parameter entity declarations
		| NOTATION	-- ^ for notations
		| CONDSECT	-- ^ for INCLUDEs, IGNOREs and peRefs: attr: type
		                --
				--  type = INCLUDE, IGNORE or %...;
		| NAME		-- ^ attr: name
		                --
				--  for lists of names in notation types or nmtokens in enumeration types
		| PEREF		-- ^ for Parameter Entity References in DTDs
		  deriving (Eq, Ord, Show, Read)

-- -----------------------------------------------------------------------------
--
-- useful type definitions

-- | Attribute list
type Attributes	= AssocList String String

-- | Tag name
type TagName	= QName

-- | Attribute name
type AttrName	= QName

-- -----------------------------------------------------------------------------
--
-- |
-- Namespace support for tag names and attribute names.
--
-- A qualified name consists of a name prefix, a local name
-- and a namespace uri.
-- All modules, which are not namespace aware, use only the 'localPart' component.
-- When dealing with namespaces, the document tree must be processed by "propagateNamespaces"
-- to split names of structure \"prefix:localPart\" and label the name with the apropriate namespace uri

data QName = QN { namePrefix	:: String	-- ^ the name prefix part of a qualified name \"namePrefix:localPart\"
		, localPart	:: String	-- ^ the local part of a qualified name \"namePrefix:localPart\"
		, namespaceUri	:: String	-- ^ the associated namespace uri
		}
	     deriving (Eq, Ord, Show, Read)

-- |
-- builds the full name \"prefix:localPart\", if prefix is not null, else the local part is the result

qualifiedName		:: QName -> String
qualifiedName n
    | null px
	= lp
    | otherwise
	= px ++ (':' : lp)
    where
    px = namePrefix n
    lp = localPart  n

-- | shortcut for 'qualifiedName'

tName	:: QName -> String
tName	= qualifiedName

-- | shortcut for 'qualifiedName'

aName	:: QName -> String
aName	= qualifiedName

-- |
-- builds the \"universal\" name, that is the namespace uri surrounded with \"{\" and \"}\" followed by the local part.

universalName	:: QName -> String
universalName n
    | null ns
	= lp
    | otherwise
	= '{' : (ns ++ ('}' : lp))
    where
    ns = namespaceUri n
    lp = localPart    n

-- |
-- constructs a simple, namespace unaware name, 'namePrefix' and 'namespaceUri' are set to the empty string.

mkName	:: String -> QName
mkName s
    = QN { namePrefix	= ""
	 , localPart	= s
	 , namespaceUri	= ""
	 }

-- |
-- constructs a simple name, with prefix and localPart but without a namespace uri.
--
-- see also 'mkName', 'mkNsName'

mkPrefixLocalPart	:: String -> String -> QName
mkPrefixLocalPart p l
    = QN { namePrefix	= p
	 , localPart	= l
	 , namespaceUri	= ""
	 }

-- |
-- constructs a simple, namespace aware name, with prefix:localPart as first parameter, namspace uri as second.
--
-- see also 'mkName', mkPrefixLocalPart

mkNsName	:: String -> String -> QName
mkNsName n ns
    = QN { namePrefix	= p
	 , localPart	= l
	 , namespaceUri	= ns
	 }
      where
      (x1, x2) = span (/= ':') n
      (p, l)
	  | null x2	= ("", x1)
	  | otherwise	= (x1, tail x2)


-- -----------------------------------------------------------------------------
--
-- Constants for error levels

-- | no error, everything is ok
c_ok	:: Int
c_ok	= 0

-- | Error level for XError, type warning
c_warn  :: Int
c_warn  = c_ok + 1

-- | Error level for XError, type error
c_err   :: Int
c_err   = c_warn + 1

-- | Error level for XError, type fatal error
c_fatal :: Int
c_fatal = c_err + 1

-- -----------------------------------------------------------------------------


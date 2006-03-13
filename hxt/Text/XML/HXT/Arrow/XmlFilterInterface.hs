-- |
-- interface for lifting HXT filter to list arrows
--
-- version: $Id$

module Text.XML.HXT.Arrow.XmlFilterInterface
    ( module Text.XML.HXT.Arrow.XmlFilterInterface )
where

import           Text.XML.HXT.DOM.XmlKeywords
import           Text.XML.HXT.DOM.TypeDefs
import qualified Text.XML.HXT.DOM.EditFilters            as EF
import qualified Text.XML.HXT.Parser.HtmlParsec          as HP
import qualified Text.XML.HXT.Parser.XmlParser           as XP
import qualified Text.XML.HXT.Validator.ValidationFilter as VA
import qualified Text.XML.HXT.XPath                      as PT

import Control.Arrow
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowTree

import Text.XML.HXT.Arrow.XmlArrow

canonicalizeAllNodes
 , canonicalizeForXPath
 , collapseXText
 , collapseAllXText
 , indentDoc
 , escapeXmlDoc
 , escapeXmlText
 , escapeXmlAttrValue
 , numberLinesInXmlDoc
 , treeRepOfXmlDoc
 , haskellRepOfXmlDoc
 , addHeadlineToXmlDoc	:: ArrowList a => a XmlTree XmlTree

addHeadlineToXmlDoc	= arrL EF.addHeadlineToXmlDoc

-- |
-- canonicalize tree and remove comments and \<?xml ... ?> declarations
--
-- see 'canonicalizeTree'

canonicalizeAllNodes	= arrL EF.canonicalizeAllNodes

-- |
-- Canonicalize a tree for XPath
-- Comment nodes are not removed
--
-- see 'canonicalizeTree'

canonicalizeForXPath	= arrL EF.canonicalizeForXPath

-- |
-- Applies collapseXText recursively.
--
--
-- see also : 'collapseXText'

collapseAllXText	= arrL EF.collapseAllXText

-- |
-- Collects sequences of child XText nodes into one XText node.

collapseXText		= arrL EF.collapseXText

-- |
-- convert the special XML chars in an attribute value into
-- charachter references. Not only the XML specials but also \\n, \\r and \\t are converted
--
-- see also: 'excapeXmlDoc', 'escapeXmlText'

escapeXmlAttrValue	= arrL EF.escapeXmlAttrValue

-- |
-- convert the special XML chars \", \<, \>, & and \' in a document to char references,
-- attribute values are converted with 'escapeXmlAttrValue'
--
-- see also: 'escapeXmlText', 'escapeXmlAttrValue'

escapeXmlDoc		= arrL EF.escapeXmlDoc

-- |
-- convert the special XML chars in a text or comment node
-- into character references
--
-- see also 'escapeXmlDoc'

escapeXmlText		= arrL EF.escapeXmlText

-- |
-- convert a document into a Haskell representation (with show).
--
-- Useful for debugging and trace output.
-- see also : 'treeRepOfXmlDoc', 'numberLinesInXmlDoc'

haskellRepOfXmlDoc	= arrL EF.haskellRepOfXmlDoc

-- |
-- filter for indenting a document tree for pretty printing.
--
-- the tree is traversed for inserting whitespace for tag indentation.
--
-- whitespace is only inserted or changed at places, where it isn't significant,
-- is's not inserted between tags and text containing non whitespace chars.
--
-- whitespace is only inserted or changed at places, where it's not significant.
-- preserving whitespace may be controlled in a document tree
-- by a tag attribute @xml:space@
--
-- allowed values for this attribute are @default | preserve@.
--
-- input is a complete document tree.
-- result the semantically equivalent formatted tree.
--
--
-- see also : 'removeDocWhiteSpace'

indentDoc		= arrL EF.indentDoc

-- |
-- convert a document into a text and add line numbers to the text representation.
-- 
-- Result is a root node with a single text node as child.
-- Useful for debugging and trace output.
-- see also : 'haskellRepOfXmlDoc', 'treeRepOfXmlDoc'

numberLinesInXmlDoc	= arrL EF.numberLinesInXmlDoc

-- |
-- convert a document into a text representation in tree form.
--
-- Useful for debugging and trace output.
-- see also : 'haskellRepOfXmlDoc', 'numberLinesInXmlDoc'

treeRepOfXmlDoc		= arrL EF.treeRepOfXmlDoc

-- ------------------------------------------------------------

-- |
-- remove Comments: @none `when` isCmt@

removeComment		:: ArrowXml a => a XmlTree XmlTree
removeComment		= none `when` isCmt

-- |
-- remove all comments recursively

removeAllComment	:: ArrowXml a => a XmlTree XmlTree
removeAllComment	= processBottomUp removeComment

-- |
-- simple filter for removing whitespace.
--
-- no check on sigificant whitespace, e.g. in HTML \<pre\>-elements, is done.
--
--
-- see also : 'removeAllWhiteSpace', 'removeDocWhiteSpace'

removeWhiteSpace	:: ArrowXml a => a XmlTree XmlTree
removeWhiteSpace	= none `when` hasText (all (`elem` " \t\n"))

-- |
-- simple recursive filter for removing all whitespace.
--
-- removes all text nodes in a tree that consist only of whitespace.
--
--
-- see also : 'removeWhiteSpace', 'removeDocWhiteSpace'

removeAllWhiteSpace	:: ArrowXml a => a XmlTree XmlTree
removeAllWhiteSpace	= processBottomUp removeWhiteSpace

-- |
-- filter for removing all not significant whitespace.
--
-- the tree traversed for removing whitespace between elements,
-- that was inserted for indentation and readability.
-- whitespace is only removed at places, where it's not significat
-- preserving whitespace may be controlled in a document tree
-- by a tag attribute @xml:space@
--
-- allowed values for this attribute are @default | preserve@
--
-- input is root node of the document to be cleaned up
-- output the semantically equivalent simplified tree
--
--
-- see also : 'indentDoc', 'removeAllWhiteSpace'

removeDocWhiteSpace	:: ArrowXml a => a XmlTree XmlTree
removeDocWhiteSpace	= arrL EF.removeDocWhiteSpace

-- ------------------------------------------------------------

-- |
-- converts a CDATA section node into a normal text node

transfCdata		:: ArrowXml a => a XmlTree XmlTree
transfCdata		= (getCdata >>> mkText) `when` isCdata

-- |
-- converts CDATA sections in whole document tree into normal text nodes

transfAllCdata		:: ArrowXml a => a XmlTree XmlTree
transfAllCdata		= processBottomUp transfCdata

-- |
-- converts character references to normal text

transfCharRef		:: ArrowXml a => a XmlTree XmlTree
transfCharRef		= (getCharRef >>> arr (\ i -> [toEnum i]) >>> mkText) `when` isCharRef

-- |
-- recursively converts all character references to normal text

transfAllCharRef	:: ArrowXml a => a XmlTree XmlTree
transfAllCharRef	= processBottomUp transfCharRef

-- ------------------------------------------------------------

parseXmlDoc			:: ArrowXml a => a (String, String) XmlTree
parseXmlDoc			=  arr2L XP.parseXmlDocument

parseXmlContent			:: ArrowXml a => a String XmlTree
parseXmlContent			=  arrL XP.xread

parseXmlEntityEncodingSpec
  , parseXmlDocEncodingSpec
  , substXmlEntityRefs		:: ArrowXml a => a XmlTree XmlTree

parseXmlDocEncodingSpec		= arrL XP.parseXmlDocEncodingSpec
parseXmlEntityEncodingSpec	= arrL XP.parseXmlEntityEncodingSpec

parseXmlAttrValue		:: ArrowXml a => String -> a XmlTree XmlTree
parseXmlAttrValue context	= arrL (XP.parseXmlAttrValue context)

parseXmlGeneralEntityValue	:: ArrowXml a => String -> a XmlTree XmlTree
parseXmlGeneralEntityValue context
				= arrL (XP.parseXmlGeneralEntityValue context)

substXmlEntityRefs		= arrL XP.substXmlEntities

-- ------------------------------------------------------------

parseHtmlDoc			:: ArrowList a => a (String, String) XmlTree
parseHtmlDoc			= arr2L HP.parseHtmlDocument

parseHtmlContent		:: ArrowList a => a String XmlTree
parseHtmlContent		= arrL  HP.parseHtmlContent

substHtmlEntityRefs		:: ArrowList a => a XmlTree XmlTree
substHtmlEntityRefs		= arrL HP.substHtmlEntities

-- ------------------------------------------------------------

validateDoc
  , transformDoc		:: ArrowList a => a XmlTree XmlTree

validateDoc			= arrL VA.validate
transformDoc			= arrL VA.transform

-- ------------------------------------------------------------

getXPath			:: ArrowList a => String -> a XmlTree XmlTree
getXPath query			= arrL (PT.getXPath query)

-- ------------------------------------------------------------

-- |
-- parse a string as HTML content, substitute all HTML entity refs and canonicalize tree
-- (substitute char refs, ...)

hread			:: ArrowXml a => a String XmlTree
hread
    = parseHtmlContent
      >>>
      processTopDown substHtmlEntityRefs
      >>>
      processTopDown ( none `when` isError )
      >>>
      canonicalizeAllNodes

-- |
-- parse a string as XML content, substitute all predefined XML entity refs and canonicalize tree
-- (substitute char refs, ...)

xread			:: ArrowXml a => a String XmlTree
xread
    = parseXmlContent
      >>>
      processTopDown substXmlEntityRefs
      >>>
      canonicalizeAllNodes


-- ------------------------------------------------------------

hasXmlPi		:: ArrowXml a => a XmlTree XmlTree
hasXmlPi
    = getChildren
      >>>
      isPi
      >>>
      hasName t_xml

addXmlPi		:: ArrowXml a => a XmlTree XmlTree
addXmlPi
    = insertChildrenAt 0 ( ( mkPi (mkSNsName t_xml) none
			     >>>
			     addAttr a_version "1.0"
			   )
			   <+>
			   txt "\n"
			 )
      `whenNot`
      hasXmlPi

addXmlPiEncoding	:: ArrowXml a => String -> a XmlTree XmlTree
addXmlPiEncoding enc
    = processChildren ( addAttr a_encoding enc
		        `when`
			( isPi >>> hasName t_xml )
		      )
-- ------------------------------------------------------------

-- ------------------------------------------------------------
--
-- protocol handler utility functions
--
-- Version : $Id$

module Text.XML.HXT.Parser.ProtocolHandlerUtil
    ( parseContentType
    )

where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.DOM.Util
    ( stringToUpper
    )

import Text.ParserCombinators.Parsec
    ( Parser
    , anyChar
    , char
    , many
    , many1
    , noneOf
    , oneOf
    , string
    , (<|>)
    )



import qualified Text.ParserCombinators.Parsec
    ( try		-- naming conflicts GHC.Extensions.try and Parsec.try
    )

-- ------------------------------------------------------------
--
-- try to extract charset spec from Content-Type header
-- e.g. "text/html; charset=ISO-8859-1"

parseContentType	:: Parser XmlTrees
parseContentType
    = Text.ParserCombinators.Parsec.try ( do
		   mimeType <- ( do
				 mt <- many (noneOf ";")
				 return (xattr transferMimeType mt)
			       )
		   charset  <- ( do
				 char ';'
				 many  (oneOf " \t'")
				 string "charset="
				 cs <- many1 anyChar
				 return (xattr transferEncoding (stringToUpper cs))
			       )
		   return (mimeType ++ charset)
		 )
      <|>
      ( do
	mimeType <- many anyChar
	return (xattr transferMimeType mimeType)
      )

-- ------------------------------------------------------------


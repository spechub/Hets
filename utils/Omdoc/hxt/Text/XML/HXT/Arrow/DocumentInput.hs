-- |
-- state arrows for document input
--
-- version $Id$

module Text.XML.HXT.Arrow.DocumentInput
    ( module Text.XML.HXT.Arrow.DocumentInput )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowTree
import Control.Arrow.ArrowIO


import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.DOM.Unicode
    ( getEncodingFct
    , guessEncoding
    , normalizeNL
    )

import qualified Text.XML.HXT.IO.GetFILE	as FILE
import qualified Text.XML.HXT.IO.GetHTTPNative	as HTTP
import qualified Text.XML.HXT.IO.GetHTTPCurl	as CURL

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
    ( parseXmlDocEncodingSpec
    , parseXmlEntityEncodingSpec
    )

import Data.Maybe

-- ----------------------------------------------------------

protocolHandlers	:: AssocList String (IOSArrow XmlTree XmlTree)
protocolHandlers
    = [ ("file",	getFileContents)
      , ("http",	getHttpContents)
      ]

getProtocolHandler	:: IOSArrow String (IOSArrow XmlTree XmlTree)
getProtocolHandler
    = arr (\ s -> lookupDef getUnsupported s protocolHandlers)

getUnsupported		:: IOSArrow XmlTree XmlTree
getUnsupported
    = perform ( getAttrValue a_source
		>>>
		arr (("unsupported protocol in URI " ++) . show)
		>>>
		applyA (arr issueFatal)
	      )
      >>>
      setDocumentStatusFromSystemState "accessing documents"
	
getFileContents		:: IOSArrow XmlTree XmlTree
getFileContents
    = applyA ( getAttrValue transferURI
	       >>>
	       getPathFromURI
	       >>>
	       arrIO FILE.getCont
	       >>>
	       ( arr addError		-- io error occured
		 |||
		 arr addContent	-- content read
	       )
	     )
      where
      addError		:: String -> IOSArrow XmlTree XmlTree
      addError e
	  = issueFatal e
	    >>>
	    setDocumentStatusFromSystemState "accessing documents"

      addContent	:: String -> IOSArrow XmlTree XmlTree
      addContent c
	  = replaceChildren (txt c)
	    >>>
	    addAttr transferMessage "OK"
	    >>>
	    addAttr transferStatus "200"

getHttpContents		:: IOSArrow XmlTree XmlTree
getHttpContents
    = applyA ( ( getAttrValue transferURI
		 &&&
		 getParamString a_proxy
	       )
	       >>>
	       applyA ( getParamInt 0 a_use_curl
			>>>
			ifP (==0)
			  ( constA $ arrIO2 HTTP.getCont )		-- native http
			  ( constA $
			    ( getParamString a_options_curl &&& this )
			    >>>
			    arrIO3 CURL.getCont
			  )
		      )
	       >>>
	       ( arr addError
		 |||
		 arr addContent
	       )
	     )
      where
      addError		:: String -> IOSArrow XmlTree XmlTree
      addError e
	  = issueFatal e
	    >>>
	    setDocumentStatusFromSystemState "accessing documents"

      addContent	:: (AssocList String String, String) -> IOSArrow XmlTree XmlTree
      addContent (al, c)
	  = replaceChildren (txt c)
	    >>>
	    seqA (map (uncurry addAttr) al)

getURIContents		:: IOSArrow XmlTree XmlTree
getURIContents
    = applyA ( ( getAttrValue a_source			-- compute absolute URI
		 >>>
		 mkAbsURI
		 >>>
		 arr (setParamString transferURI)
	       )
	       `orElse`
	       ( getAttrValue a_source
		 >>>
		 arr (("illegal URI : " ++) . show)
		 >>>
		 arr issueFatal
	       )
	     )
      >>>
      applyA ( getParamString transferURI
	       >>>
	       arr (addAttr transferURI)
	     )
      >>>
      ( applyA ( getParamString transferURI		-- compute the handler and call it
		 >>>
		 traceString 2 (("getURIContents: reading" ++) . show)
		 >>>
		 getSchemeFromURI
		 >>>
		 getProtocolHandler
	       )
	`orElse` this					-- don't change tree, when no handler can be found
      )
      >>>
      setDocumentStatusFromSystemState "getURIContents"

setBaseURIFromDoc	:: IOSArrow XmlTree XmlTree
setBaseURIFromDoc
    = perform ( getAttrValue transferURI
		>>>
		setBaseURI
	      )

getXmlContents		:: IOSArrow XmlTree XmlTree
getXmlContents
    = getXmlContents' parseXmlDocEncodingSpec
      >>>
      setBaseURIFromDoc

getXmlEntityContents		:: IOSArrow XmlTree XmlTree
getXmlEntityContents
    = getXmlContents' parseXmlEntityEncodingSpec
      >>>
      setBaseURIFromDoc

getXmlContents'		:: IOSArrow XmlTree XmlTree -> IOSArrow XmlTree XmlTree
getXmlContents' parseEncodingSpec
    = ( getURIContents
	>>>
	parseEncodingSpec
	>>>
	filterErrorMsg
	>>>
	decodeDocument
	>>>
	perform ( getAttrValue transferURI
		  >>>
		  traceString 1 (("getXmlContents: content read and decoded for " ++) . show)
		)
	>>>
	traceTree
	>>>
	traceSource
      )
      `when`
      isRoot

-- ------------------------------------------------------------

getEncoding	:: IOSArrow XmlTree String
getEncoding
    = catA [ xshow getChildren			-- 1. guess: guess encoding by looking at the first few bytes
	     >>>
	     arr guessEncoding
	   , getAttrValue transferEncoding	-- 2. guess: take the transfer encoding
	   , getAttrValue a_encoding		-- 4. guess: take encoding parameter in root node
	   , getParamString a_encoding		-- 5. guess: take encoding parameter in global state
	   , constA utf8			-- default : utf8
	   ]
      >. (head . filter (not . null))		-- make the filter deterministic: take 1. entry from list of guesses


decodeDocument	:: IOSArrow XmlTree XmlTree
decodeDocument
    = applyA ( getEncoding
	       >>>
	       arr encArr
	     )
      `when`
      isRoot
    where
    encArr	:: String -> IOSArrow XmlTree XmlTree
    encArr enc	= maybe notFound found . getEncodingFct $ enc
	where
	found ef = traceMsg 2 ("decodeDocument: encoding is " ++ show enc)
		   >>>
		   processChildren (changeText (normalizeNL . ef))
		   >>>
		   addAttr transferEncoding enc

	notFound = issueFatal ("encoding scheme not supported: " ++ show enc)
		   >>>
		   setDocumentStatusFromSystemState "decoding document"

-- ------------------------------------------------------------

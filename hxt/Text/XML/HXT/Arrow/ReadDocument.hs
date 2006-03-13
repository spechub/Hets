-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.ReadDocument
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt (uwe\@fh-wedel.de)
   Stability  : experimental
   Portability: portable
   Version    : $Id$

Compound arrows for reading a document

-}

-- ------------------------------------------------------------

module Text.XML.HXT.Arrow.ReadDocument
    ( readDocument )
where

import Control.Arrow.ListArrows

import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.XmlStateFilterInterface

import Text.XML.HXT.RelaxNG.Validator	( validateDocumentWithRelaxSchema )

-- ------------------------------------------------------------

{- |
the main document input filter

this filter can be configured by an option list, a value of type "Attributes"

available options:

* 'a_parse_html': use HTML parser, else use XML parser (default)

- 'a_validate' : validate document againsd DTD, else skip validation (default)

- 'a_relax_schema' : validate document with Relax NG, the options value is the schema URI
                     this implies using XML parser, no validation against DTD, and canonicalisation

- 'a_check_namespaces' : check namespaces, else skip namespace processing (default)

- 'a_canonicalize' : canonicalize document (default), else skip canonicalization

- 'a_preserve_comment' : preserve comments during canonicalization, else remove comments (default)

- 'a_remove_whitespace' : remove all whitespace, used for document indentation, else skip this step (default)

- 'a_indent' : indent document by inserting whitespace, else skip this step (default)

- 'a_issue_warnings' : issue warnings, when parsing HTML (default), else ignore HTML parser warnings

- 'a_issue_errors' : issue all error messages on stderr (default), or ignore all error messages (default)

- 'a_trace' : trace level: values: 0 - 4

- 'a_proxy' : proxy for http access, e.g. www-cache:3128

- 'a_use_curl' : for http access via external programm curl, default is native HTTP access

- 'a_options_curl' : more options for external program curl

- 'a_encoding' : default document encoding ('utf8', 'isoLatin1', 'usAscii', ...)

all attributes not evaluated by readDocument are stored in the created document root node for easy access of the various
options in e.g. the input\/output modules

examples:

> readDocument [ ] "test.xml"

reads document, no validation, no namespace propagation, only canonicalization is performed 

> readDocument [ (a_validate, "1")
>              , (a_encoding, isoLatin1)
>              ] "test.xml"

reads document \"test.xml\" with validation, default encoding 'isoLatin1'

> readDocument [ (a_parse_html,     "1")
>              , (a_proxy,          "www-cache:3128")
>              , (a_curl,           "1")
>              , (a_issue_warnings, "0")
>              ] "http://www.haskell.org/"

reads Haskell homepage with HTML parser ignoring any warnings, with http access via external program curl and proxy \"www-cache\" at port 3128

> readDocument [ (a_validate,          "1")
>              , (a_check_namespace,   "1")
>              , (a_remove_whitespace, "1")
>              , (a_trace,             "2")
>              ] "http://www.w3c.org/"

read w3c home page (xhtml), validate and check namespaces, remove whitespace between tags, trace activities with level 2

for minimal complete examples see 'writeDocument' and 'runX', the main starting point for running an XML arrow.
-}

readDocument	:: Attributes -> String -> IOSArrow b XmlTree
readDocument userOptions src
    = traceLevel
      >>>
      getDocumentContents remainingOptions src
      >>>
      parse
      >>>
      checknamespaces
      >>>
      canonicalize
      >>>
      whitespace
      >>>
      relax
      >>>
      traceMsg 1 ("readDocument: " ++ show src ++ " processed")
      >>>
      traceSource
      >>>
      traceTree
    where
    parse
	| validateWithRelax		= parseXmlDocument False		-- for Relax NG use XML parser without validation

	| hasOption a_parse_html	= parseHtmlDocument			-- parse as HTML
					  (hasOption a_issue_warnings)

	| otherwise			= parseXmlDocument
					  (hasOption a_validate)		-- parse as XML

    checknamespaces
	| hasOption a_check_namespaces
	  ||
	  validateWithRelax		= propagateAndValidateNamespaces
	| otherwise			= this

    canonicalize
	| validateWithRelax		= canonicalizeAllNodes
	| hasOption a_canonicalize
	  &&
	  hasOption a_preserve_comment	= canonicalizeForXPath
	| hasOption a_canonicalize	= canonicalizeAllNodes
	| otherwise			= this

    relax
	| validateWithRelax		= validateDocumentWithRelaxSchema remainingOptions relaxSchema
	| otherwise			= this

    whitespace
	| hasOption a_remove_whitespace	= removeDocWhiteSpace
	| otherwise			= this

    traceLevel
	= maybe this (setTraceLevel . read) . lookup a_trace $ options

    validateWithRelax
	= hasEntry a_relax_schema $ options

    relaxSchema
	= lookup1 a_relax_schema $ options

    hasOption n
	= (`elem` ["1", "True", "true", "Yes", "yes"]) . lookupDef "" n $ options

    options = addEntries userOptions defaultOptions

    defaultOptions
	= [ ( a_parse_html,		v_0 )
	  , ( a_validate,		v_0 )
	  , ( a_issue_warnings,		v_1 )
	  , ( a_check_namespaces,	v_0 )
	  , ( a_canonicalize,		v_1 )
	  , ( a_preserve_comment,	v_0 )
	  , ( a_remove_whitespace,	v_0 )
	  ]

    remainingOptions
	 = filter (not . flip hasEntry defaultOptions . fst) options

-- ------------------------------------------------------------

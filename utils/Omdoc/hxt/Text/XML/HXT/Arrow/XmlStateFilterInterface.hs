-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.XmlStateFilterInterface
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt
   Maintainer : uwe@fh-wedel.de
   Stability  : experimental
   Portability: portable
   Version    : $Id$

Compound arrows for reading, parsing, validating and writing XML documents

All arrows use IO and a global state for options, errorhandling, ...
-}

-- ------------------------------------------------------------

module Text.XML.HXT.Arrow.XmlStateFilterInterface
    ( parseXmlDocument
    , parseHtmlDocument
    , validateDocument
    , propagateAndValidateNamespaces
    , readDocument
    , writeDocument
    )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowState
import Control.Arrow.ArrowTree
-- import Control.Arrow.ArrowIO
import Control.Arrow.IOStateListArrow

import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.GeneralEntitySubstitution
import Text.XML.HXT.Arrow.DocumentInput
import Text.XML.HXT.Arrow.DocumentOutput


-- these modules become obsolete, when DTD processing is rewritten
import qualified Control.Monad.MonadStateIO        as MonadStateIO
import qualified Text.XML.HXT.DOM.XmlState         as XS
import qualified Text.XML.HXT.Parser.DTDProcessing as DP

-- ------------------------------------------------------------
--
-- the horrible part: the interface to XmlStateFilter
-- with parameter conversion and error message propagation

getParams		:: IOSArrow XmlTree (AssocList String XmlTrees)
getParams
    = listA ( applyA ( getState
		       >>>
		       arr getPar
		     )
	    )
    where
    getPar (XIOS m) = catA [get1Par n | (n, _) <- m]	-- here a filter must be installed, if not all parameter have to be transfered into state
    get1Par n       = constA n &&& listA (getParam n)

runXmlStateFilter	:: XS.XmlStateFilter () -> IOSArrow (AssocList String XmlTrees, XmlTree) (AssocList String XmlTrees, XmlTrees)
runXmlStateFilter xsf
    = IOSLA $ \ s ~(sysState, t) ->
      let
      (MonadStateIO.STIO cmd) = do
				XS.setSysErrorHandler XS.errorMsgLoggingAndToStderr	-- to be changed into errorMsgLogging when testing is finished
				xsf $ t
      initialSysState = XS.changeSysStateAttrs (const sysState) XS.initialSysState
      in
      do (res, finalState) <- cmd (XS.XmlState initialSysState ())
	 let finalSysState = XS.sysStateAttrs . XS.sysState $ finalState
	 let newSysState   = updateSysState finalSysState sysState
	 return (s, [(newSysState, res)])
    where
							-- update only those attributes that have been changed
    updateSysState	:: AssocList String XmlTrees -> AssocList String XmlTrees -> AssocList String XmlTrees
    updateSysState ns ss
	= [ p | p@(n, v) <- ns, not (hasEntry n ss) || lookup1 n ns /= v ]


setXmlStateParams	:: IOSArrow (AssocList String XmlTrees) (AssocList String XmlTrees)
setXmlStateParams
    = applyA (arr setPar)
    where
    setPar as		= seqA [set1Par n ts | (n,ts) <- as ]
    set1Par n ts	= perform (constA ts >>> setParamList n)


liftXmlStateFilter	:: XS.XmlStateFilter () -> IOSArrow XmlTree XmlTree
liftXmlStateFilter xsf
    = traceMsg 2 "calling XmlStateFilter"
      >>>
      ( getParams &&& this )
      >>>
      runXmlStateFilter xsf
      >>>
      ( ( setXmlStateParams
	  >>>
	  getErrors
	)
	***
	this
      )
      >>>
      arrL snd
      >>>
      traceMsg 2 "XmlStateFilter call finished"
      >>>
      traceSource
      >>>
      traceTree
    where
    getErrors :: IOSArrow b b
    getErrors = perform ( getParam a_error_log
			  >>>
			  filterErrorMsg
			)
		>>>
		unsetParam a_error_log

-- ------------------------------------------------------------

-- the last  State filter: DTD processing

processDTD		:: IOSArrow XmlTree XmlTree
processDTD		= liftXmlStateFilter DP.processDTD


-- ------------------------------------------------------------

{- | 
XML parser

Input tree must be a root tree with a text tree as child containing the document to be parsed.
The parser generates from the input string a tree of a wellformed XML document,
processes the DTD (parameter substitution, conditional DTD parts, ...) and
substitutes all general entity references. Next step is character reference substitution.
Last step is the document validation.
Validation can be controlled by an extra parameter.

Example:

> parseXmlDocument True    -- parse and validate document
>
> parseXmlDocument False   -- only parse document, don't validate

This parser is useful for applications processing correct XML documents.
-}

parseXmlDocument	:: Bool -> IOSArrow XmlTree XmlTree
parseXmlDocument validate
    = ( replaceChildren ( ( getAttrValue a_source
			    &&&
			    xshow getChildren
			  )
			  >>>
			  parseXmlDoc
			  >>>
			  filterErrorMsg
			)
	>>>
	setDocumentStatusFromSystemState "parse XML document"
	>>>
	processDTD
	>>>
	processGeneralEntities
	>>>
	transfAllCharRef
	>>>
	( if validate
	  then validateDocument
	  else this
	)
      )
      `when` documentStatusOk

-- ------------------------------------------------------------

{- | 
HTML parser

Input tree must be a root tree with a text tree as child containing the document to be parsed.
The parser tries to parse everything as HTML, if the HTML document is not wellformed XML or if
errors occur, warnings are generated. The warnings can be issued, or suppressed.

Example: @ parseHtmlDocument True @ : parse document and issue warnings

This parser is useful for applications like web crawlers, where the pages may contain
arbitray errors, but the application is only interested in parts of the document, e.g. the plain text.

-}

parseHtmlDocument	:: Bool -> IOSArrow XmlTree XmlTree
parseHtmlDocument warnings
    = ( perform ( getAttrValue a_source >>> traceString 1 (("parseHtmlDoc: parse HTML document " ++) . show) )
	>>>
	replaceChildren ( ( getAttrValue a_source		-- get source name
			    &&&
			    xshow getChildren
			  ) 					-- get string to be parsed
			  >>>
			  parseHtmlDoc				-- run parser
			  >>>
			  processTopDown substHtmlEntityRefs	-- substitute entity refs
			)
	>>>
	processTopDownWithAttrl ( if warnings		-- remove warnings inserted by parser and entity subst
				  then filterErrorMsg
				  else ( none
					 `when`
					 isError
				       )
				)
	>>>
	setDocumentStatusFromSystemState "parse HTML document"
	>>>
	traceTree
	>>>
	traceSource
	>>>
	perform ( getAttrValue a_source >>> traceString 1 (\ src -> "parse HTML document " ++ show src ++ " finished") )
      )
      `when` documentStatusOk

-- ------------------------------------------------------------

{- | Document validation

Input must be a complete document tree. The document
is validated with respect to the DTD spec.
Only useful for XML documents containing a DTD.

If the document is valid, it is transformed with respect to the DTD,
normalization of attribute values, adding default values, sorting attributes by name,...

If no error was found, result is the normalized tree,
else the error status is set in the list of attributes
of the root node \"\/\" and the document content is removed from the tree.

-}

validateDocument	:: IOSArrow XmlTree XmlTree
validateDocument
    = ( traceMsg 1 "validating document"
	>>>
	perform ( validateDoc
		  >>>
		  filterErrorMsg
		)
	>>>
	setDocumentStatusFromSystemState "document validation"
	>>>
	transformDoc
	>>>
	traceMsg 1 "document validated"
	>>>
	traceSource
	>>>
	traceTree
      )
      `when`
      documentStatusOk
      
-- ------------------------------------------------------------

{- | Namespace propagation

Input must be a complete document tree. The namespace declarations
are evaluated and all element and attribute names are processed by
splitting the name into prefix, local part and namespace URI.

Naames are checked with respect to the XML namespace definition

If no error was found, result is the unchanged input tree,
else the error status is set in the list of attributes
of the root node \"\/\" and the document content is removed from the tree.


-}

propagateAndValidateNamespaces	:: IOSArrow XmlTree XmlTree
propagateAndValidateNamespaces
    = ( traceMsg 1 "propagating namespaces"
	>>>
	propagateNamespaces
	>>>
	traceTree
	>>>
	traceSource
	>>>
	traceMsg 1 "validating namespaces"
	>>>
	( setDocumentStatusFromSystemState "namespace propagation"
	  `when`
	  ( validateNamespaces >>> perform filterErrorMsg )
	)
	>>>
	traceMsg 1 "namespace validation finished"
      )
      `when`
      documentStatusOk

-- ------------------------------------------------------------

{- |
the main document input filter

this filter can be configured by an option list, a value of type "Attributes"

available options:

* 'a_parse_html': use HTML parser, else use XML parser (default)

- 'a_validate' : validate document, else skip validation (default)

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

the attribute list is stored in the global state component for easy access of the various
options in the input\/output modules

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
    = root [] []
      >>>
      traceLevel
      >>>
      addAttr a_source src
      >>>
      seqA (map (uncurry addAttr) remainingOptions)				-- add all other options to doc root
      >>>									-- getXmlContents needs some options
      traceMsg 1 ("readDocument: start processing document " ++ show src)
      >>>
      getXmlContents
      >>>
      parse
      >>>
      checknamespaces
      >>>
      canonicalize
      >>>
      whitespace
      >>>
      traceMsg 1 ("readDocument: " ++ show src ++ " processed")
      >>>
      traceSource
      >>>
      traceTree
    where
    parse
	| hasOption a_parse_html	= parseHtmlDocument			-- parse as HTML
					  (hasOption a_issue_warnings)

	| otherwise			= parseXmlDocument
					  (hasOption a_validate)		-- parse as XML

    checknamespaces
	| hasOption a_check_namespaces	= propagateAndValidateNamespaces
	| otherwise			= this

    canonicalize
	| hasOption a_canonicalize
	  &&
	  hasOption a_preserve_comment	= canonicalizeForXPath
	| hasOption a_canonicalize	= canonicalizeAllNodes
	| otherwise			= this

    whitespace
	| hasOption a_remove_whitespace	= removeDocWhiteSpace
	| otherwise			= this

    traceLevel
	= maybe this (setTraceLevel . read) . lookup a_trace $ options

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

{- |
the main filter for writing documents

this filter can be configured by an option list like 'readDocument'

usage: @ writeDocument optionList destination @

if @ destination @ is the empty string or \"-\" stdout is used as output device

available options are

* 'a_indent' : indent document for readability, (default: no indentation)

- 'a_remove_whitespace' : remove all redundant whitespace for shorten text (default: no removal)

- 'a_output_encoding' : encoding of document, default is 'a_encoding' or 'utf8'

- 'a_output_xml' : (default) issue XML: quote special XML chars \>,\<,\",\',&
                   add XML processing instruction
                   and encode document with respect to 'a_output_encoding',
                   if explicitly switched of, the plain text is issued, this is useful
                   for non XML output, e.g. generated Haskell code, LaTex, Java, ...

- 'a_show_tree' : show tree representation of document (for debugging)

- 'a_show_haskell' : show Haskell representaion of document (for debugging)

 a minimal main program for copying a document
 has the following structure:

> module Main
> where
> 
> import Text.XML.HXT.Arrow
> 
> main        :: IO ()
> main
>     = do
>       runX ( readDocument  [] "hello.xml"
>              >>>
>              writeDocument [] "bye.xml"
>            )
>       return ()

an example for copying a document to standard output with tracing and evaluation of
error code is:

> module Main
> where
> 
> import Text.XML.HXT.Arrow
> import System.Exit
> 
> main        :: IO ()
> main
>     = do
>       [rc] <- runX ( readDocument  [ (a_trace, "1")
>                                    ] "hello.xml"
>                      >>>
>                      writeDocument [ (a_output_encoding, isoLatin1)
>                                    ] "-"        -- output to stdout
>                      >>>
>                      getErrStatus
>                    )
>       exitWith ( if rc >= c_err
>                  then ExitFailure 1
>                  else ExitSuccess
>                )
-}
writeDocument	:: Attributes -> String -> IOSArrow XmlTree XmlTree
writeDocument userOptions dst
    = perform ( traceMsg 1 ("writeDocument: destination is " ++ show dst)
		>>>
		indent
		>>>
		format
		>>>
		putXmlDocument dst
		>>>
		traceMsg 1 "writeDocument: finished"
	      )
      `when`
      documentStatusOk
    where
    indent
	| hasOption a_indent		= indentDoc			-- document indentation
	| hasOption a_remove_whitespace	= removeDocWhiteSpace		-- remove all whitespace between tags
	| otherwise			= this

    format
	| hasOption a_show_tree		= treeRepOfXmlDoc
	| hasOption a_show_haskell	= haskellRepOfXmlDoc
	| hasOption a_output_xml	= escapeXmlDoc			-- escape lt, gt, amp, quot, 
					  >>>
					  encodeDocument		-- convert doc into text with respect to output encoding
					    ( lookupDef "" a_output_encoding options )
	| otherwise			= this

    hasOption n
	= (`elem` ["1", "True", "true", "Yes", "yes"]) . lookupDef "" n $ options

    options = addEntries 
              userOptions 
	      [ ( a_indent,		v_0 )
	      , ( a_remove_whitespace,	v_0 )
	      , ( a_output_xml,		v_1 )
	      , ( a_show_tree,		v_0 )
	      , ( a_show_haskell,	v_0 )
	      ]

-- ------------------------------------------------------------

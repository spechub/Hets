-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.XmlStateFilterInterface
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt (uwe\@fh-wedel.de)
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
    , getDocumentContents
    )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowTree
import Control.Arrow.IOStateListArrow

import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.GeneralEntitySubstitution
import Text.XML.HXT.Arrow.DocumentInput
import Text.XML.HXT.Arrow.Namespace

-- currently unused
--
-- import Control.Arrow.ArrowState
-- import Control.Arrow.ArrowIO
-- import Text.XML.HXT.Arrow.DocumentOutput

-- these modules become obsolete, when DTD processing is rewritten
import qualified Control.Monad.MonadStateIO        as MonadStateIO
import qualified Text.XML.HXT.DOM.XmlState         as XS
import qualified Text.XML.HXT.Parser.DTDProcessing as DP

-- ------------------------------------------------------------
--
-- the horrible part: the interface to XmlStateFilter
-- with parameter conversion and error message propagation

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
      ( getAllParams &&& this )
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
   creates a new document root, adds all options
   as attributes to the document root and calls 'getXmlContents'
-}

getDocumentContents	:: Attributes -> String -> IOSArrow b XmlTree
getDocumentContents options src
    = root [] []
      >>>
      addAttr a_source src
      >>>
      seqA (map (uncurry addAttr) options)					-- add all options to doc root
      >>>									-- e.g. getXmlContents needs some of these
      traceMsg 1 ("readDocument: start processing document " ++ show src)
      >>>
      getXmlContents

-- ------------------------------------------------------------

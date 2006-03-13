-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.WriteDocument
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt (uwe\@fh-wedel.de)
   Stability  : experimental
   Portability: portable
   Version    : $Id$

Compound arrow for writing XML documents

-}

-- ------------------------------------------------------------

module Text.XML.HXT.Arrow.WriteDocument
    ( writeDocument )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf

import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.DocumentOutput

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

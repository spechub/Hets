-- |
-- output functions
-- implemented as filer
--
-- Version : $Id$

module Text.XML.HXT.Parser.XmlOutput
    ( numberLines

    , unparseXmlDoc
    , numberLinesInXmlDoc
    , treeRepOfXmlDoc
    , haskellRepOfXmlDoc
    , addHeadlineToXmlDoc
    , addXmlPiToDoc

    , putXmlDoc
    , putXmlDocToFile
    , putXmlTree	-- for trace output
    , putXmlSource	--  "    "     "

    , hPutXmlDoc
    , hPutXmlTree
    , hPutXmlSource

    , traceF
    , traceMsg
    , traceTree
    , traceSource
    )

where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.DOM.XmlState

import Text.XML.HXT.DOM.FormatXmlTree
    ( formatXmlContents )

import Text.XML.HXT.DOM.EditFilters
    ( indentDoc )

import Text.XML.HXT.DOM.Unicode
    ( getOutputEncodingFct )

import Data.Maybe
    ( fromMaybe )

import System.IO

-- ------------------------------------------------------------

-- |
-- convert a document tree into an output string representation
-- with respect to the output encoding.
--
-- The children of the document root are stubstituted by
-- a single text node for the text representation of the document.
--
-- Encoding of the document is performed with respect
-- to the @output-encoding@ attribute in the root node, or if not present,
-- of the @encoding@ attribute for the original input encoding.
-- If the encoding is not specified or not supported, UTF-8 is taken.

unparseXmlDoc	:: XmlFilter
unparseXmlDoc n
    = modifyChildren ((modifyText encFct $$) . xmlTreesToText) n
    where
    encFct = fromMaybe id (getOutputEncodingFct (encSpec n))

encSpec :: XmlTree -> String
encSpec n
    = head . filter (not . null)
      $ [ valueOf a_output_encoding n
	, valueOf a_encoding n
	, utf8
	]

-- ------------------------------------------------------------
--
-- add or modify a XML directive for a document
-- for specifying the encoding scheme

addXmlPiToDoc		:: XmlFilter
addXmlPiToDoc n
    = ( modifyChildren addX				-- add <?xml ...>, if neccessary
	`whenNot`
	(getChildren .> isPi t_xml)
      )
      .>
      processChildren ( addAttr a_encoding enc		-- set or replace encoding="..."
			`when`
			isPi t_xml
		      )
      $ n
    where
    enc = encSpec n
    addX cs = mkXmlDeclTree (xattr a_version "1.0") : xtext "\n" ++ cs

-- ------------------------------------------------------------

-- |
-- convert a document into a text and add line numbers to the text representation.
-- 
-- Result is a root node with a single text node as child.
-- Useful for debugging and trace output.
-- see also : 'haskellRepOfXmlDoc', 'treeRepOfXmlDoc'

numberLinesInXmlDoc	:: XmlFilter
numberLinesInXmlDoc
    = modifyChildren ((modifyText numberLines $$) . xmlTreesToText)

numberLines	:: String -> String
numberLines str
    = concat $
      zipWith (\ n l -> lineNr n ++ l ++ "\n") [1..] (lines str)
      where
      lineNr	:: Int -> String
      lineNr n	= (reverse (take 6(reverse (show n) ++ replicate 6 ' '))) ++ "  "

-- ------------------------------------------------------------

-- |
-- convert a document into a text representation in tree form.
--
-- Useful for debugging and trace output.
-- see also : 'haskellRepOfXmlDoc', 'numberLinesInXmlDoc'

treeRepOfXmlDoc		:: XmlFilter
treeRepOfXmlDoc
    = rootTag [getAttrl] [formatXmlContents]

-- |
-- convert a document into a Haskell representation (with show).
--
-- Useful for debugging and trace output.
-- see also : 'treeRepOfXmlDoc', 'numberLinesInXmlDoc'

haskellRepOfXmlDoc	:: XmlFilter
haskellRepOfXmlDoc n
    = rootTag [getAttrl] [txt $ show n] n

-- ------------------------------------------------------------

addHeadlineToXmlDoc	:: XmlFilter
addHeadlineToXmlDoc n
    = replaceChildren (xtext title ++ getChildren n ++ xtext "\n") n
      where
      headline  = "content of: " ++ valueOf a_source n
      underline = map (\_ -> '=') headline
      title     = "\n" ++ headline ++ "\n" ++ underline ++ "\n\n"

-- ------------------------------------------------------------

-- |
-- document output for standard output
--
-- see also : 'hPutXmlDoc'

putXmlDoc	:: XmlStateFilter a
putXmlDoc	= hPutXmlDoc stdout

-- |
-- document output for arbitrary files.
--
-- Result is the input document

hPutXmlDoc	:: Handle -> XmlStateFilter a
hPutXmlDoc handle t
    = do
      res <- io $ try (hPutStr handle content)
      case res of
        Left ioerr
	    -> ( issueFatal (show ioerr)
		 +++>>
		 thisM
	       ) t
	Right _
	    -> thisM t

    where
    content = xshow . getChildren $ t

-- |
-- document output on a given file name
--
-- Result is the input document
--
-- see also : 'hPutXmlDoc', 'putXmlDoc'

putXmlDocToFile	:: String -> XmlStateFilter a
putXmlDocToFile fn t
    = do
      res <- io $ try (openFile fn WriteMode)
      case res of
        Left ioerr
	    -> ( issueFatal (show ioerr)
		 +++>>
		 thisM
	       ) t
	Right h
	    -> do
	       t' <- hPutXmlDoc h t
	       io $ try (hClose h)
	       trace 2 ("document written to file: " ++ fn)
	       return t'

-- ------------------------------------------------------------

-- |
-- output of tree representation for trace

hPutXmlTree	:: Handle -> XmlStateFilter a
hPutXmlTree handle
    = performAction
      (\ n -> liftMf (treeRepOfXmlDoc
		     .>
		     addHeadlineToXmlDoc
		    )
              .>>
              hPutXmlDoc handle
              $ n
      )

putXmlTree	:: XmlStateFilter a
putXmlTree	= hPutXmlTree stdout

-- |
-- output of text representation for trace

hPutXmlSource	:: Handle -> XmlStateFilter a
hPutXmlSource handle
    = performAction
      (\ n -> liftMf ( ( rootTag
			[ sattr a_source "internal tree" ]
			[ this ]
			`whenNot` isRoot
		      )
		      .>
		      indentDoc
		      .>
		      numberLinesInXmlDoc
		      .>
		      addHeadlineToXmlDoc
		    )
              .>>
              hPutXmlDoc handle
              $ n
      )

putXmlSource	:: XmlStateFilter a
putXmlSource	= hPutXmlSource stdout

-- ------------------------------------------------------------

-- trace filter for inserting trace operations
-- into a filter sequence
--
--    * 1.parameter level : like in 'traceCmd'
--
--    - 2.parameter cmd : the output filter, e.g. putXmlTree or putXmlSource
--
--    - 3.parameter : the tree
--
--    - returns: the tree

traceF		:: Int -> XmlStateFilter a -> XmlStateFilter a
traceF level cmd
    = performAction (\ t -> traceCmd level (cmd t))

traceMsg	:: Int -> String -> XmlStateFilter a
traceMsg level msg
    = performAction (\ _ -> trace level msg)

traceTree	:: XmlStateFilter a
traceTree
    = traceF 4 (hPutXmlTree stderr)

traceSource	:: XmlStateFilter a
traceSource
    = traceF 3 (hPutXmlSource stderr)

-- ------------------------------------------------------------

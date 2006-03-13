-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.XmlIOStateArrow
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt (uwe\@fh-wedel.de)
   Stability  : experimental
   Portability: portable
   Version    : $Id$

the basic state arrows for XML processing

a state is needed for global processing options,
like encoding options, document base URI, trace levels
and error message handling

the global store is implemented as a key value pair,
keys are strings, values are state arrows, see 'XIOS'

an alias for state arrows with a 'XIOS' state is 'IOSArrow'

-}

-- ------------------------------------------------------------

module Text.XML.HXT.Arrow.XmlIOStateArrow
    ( -- * Data Types
      XIOS(..),
      IOSArrow,

      -- * Running Arrows
      emptyX,
      runX,

      -- * Global State Access
      setParamList,
      setParam,
      unsetParam,
      getParam,
      getAllParams,
      setParamArrow,
      getParamArrow,
      setParamString,
      getParamString,
      setParamInt,
      getParamInt,
      
      -- * Error Message Handling
      clearErrStatus,
      setErrStatus,
      getErrStatus,
      setErrMsgStatus,
      setErrorMsgHandler,
      errorMsgHandler,
      errorMsgStderr,
      errorMsgCollect,
      errorMsgStderrAndCollect,
      getErrorMessages,
      filterErrorMsg,
      issueWarn,
      issueErr,
      issueFatal,
      setDocumentStatus,
      setDocumentStatusFromSystemState,
      documentStatusOk,

      -- * Document Base
      setBaseURI,
      getBaseURI,
      changeBaseURI,
      setDefaultBaseURI,
      getDefaultBaseURI,
      runInLocalURIContext,

      -- * Tracing
      setTraceLevel,
      getTraceLevel,
      trace,
      traceMsg,
      traceString,
      traceSource,
      traceTree,
      traceDoc,
      traceState,

      -- * URI Manipulation
      expandURIString,
      expandURI,
      mkAbsURI,

      getFragmentFromURI,
      getPathFromURI,
      getPortFromURI,
      getQueryFromURI,
      getRegNameFromURI,
      getSchemeFromURI,
      getUserInfoFromURI
      )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowState
import Control.Arrow.ArrowTree
import Control.Arrow.ArrowIO

import Control.Arrow.IOStateListArrow

import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
    ( addHeadlineToXmlDoc
    , treeRepOfXmlDoc
    )

import Data.Maybe

import Network.URI
    ( URI
    , parseURIReference
    , nonStrictRelativeTo
    , uriScheme
    , uriPath
    , uriQuery
    , uriFragment
    , uriAuthority
    , uriRegName
    , uriPort
    , uriUserInfo
    )

import System.IO
    ( hPutStrLn
    , stderr
    )

import System.Directory
    ( getCurrentDirectory
    )

-- ------------------------------------------------------------
{- $datatypes -}

-- |
-- a generally useful state is a key-value table.
--
-- For keys 'String' is an appropriate data type, but values are of
-- different kind.
--
-- The simplest values needed to control e.g. trace, IO, ...
-- are Numbers or Strings, but it can be useful to store whole XML trees, e.g. for
-- more complex configuration data or for collecting error messages.
-- 
-- So 'XmlTree' seems to be a general solution. But sometimes it becomes
-- neccessary to store functions, e.g. for error message handling,
-- so the attribute type is an arrow (with state) for XmlTrees

newtype XIOS 		= XIOS (AssocList String (IOSArrow XmlTree XmlTree))

type IOSArrow b c	= IOSLA XIOS b c

-- ------------------------------------------------------------

-- | the empty global state, used as initial state when running an 'IOSArrow' with 'runIOSLA' or
-- 'runX'
--
-- definition: @ emptyX = XIOS [] @

emptyX			:: XIOS
emptyX			= XIOS []


-- |
-- apply an 'IOSArrow' to an empty root node using 'emptyX' as initial state
--
-- the main entry point for running a state arrow with IO
--
-- when running @ runX f@ an empty XML root node is applied to @f@.
-- usually @f@ will start with a constant arrow (ignoring the input)
--
-- for usage see examples with 'Text.XML.HXT.Arrow.XmlStateFilterInterface.writeDocument'
--
-- if input has to be feed into the arrow use 'Control.Arrow.IOStateListArrow.runIOSLA' like in @ runIOSLA f emptyX inputDoc @

runX	:: IOSArrow XmlTree c -> IO [c]
runX f
    = do
      (_finalState, res) <- runIOSLA (emptyRoot >>> f) emptyX undefined
      return res
    where
    emptyRoot    = root [] []

-- ------------------------------------------------------------

{- $params -}

-- | store a list of XML trees in global state

setParamList	:: String -> IOSArrow XmlTrees XmlTree
setParamList n
    = IOSLA $ \ (XIOS s) xs ->
      let
      s' = addEntry n (arrL $ const xs) s
      in
      return (XIOS s', xs)

-- | store a single XML tree in global state

setParam	:: String -> IOSArrow XmlTree XmlTree
setParam n
    = arr (:[]) 		-- arr (\x -> [x])
      >>>
      setParamList n

-- | remove an entry in global state, arrow input remains unchanged

unsetParam	:: String -> IOSArrow b b
unsetParam n
    = IOSLA $ \ (XIOS s) x ->
      let
      s' = delEntry n s
      in
      return (XIOS s', [x])

-- | read an attribute value from global state

getParam	:: String -> IOSArrow b XmlTree
getParam n
    = IOSLA $ \ (XIOS s) _x ->
      let
      IOSLA f = lookupDef none n s
      in
      f (XIOS s) undefined

-- | get all params from global state

getAllParams	:: IOSArrow b (AssocList String XmlTrees)
getAllParams
    = listA ( applyA ( getState
		       >>>
		       arr getPar
		     )
	    )
    where
    getPar (XIOS m) = catA [get1Par n | (n, _) <- m]	-- here a filter must be installed, if not all parameter have to be transfered into state
    get1Par n       = constA n &&& listA (getParam n)

-- | store a state arrow in global state, e.g. for error message handling

setParamArrow	:: String -> IOSArrow (IOSArrow XmlTree XmlTree) (IOSArrow XmlTree XmlTree)
setParamArrow n
    = IOSLA $ \ (XIOS s) x ->
      let
      s' = addEntry n x s
      in
      return (XIOS s', [x])

-- | read a state arrow from global state

getParamArrow	:: (IOSArrow XmlTree XmlTree) -> String -> IOSArrow b (IOSArrow XmlTree XmlTree)
getParamArrow def n
    = IOSLA $ \ (XIOS s) _x -> return (XIOS s, [lookupDef def n s])

-- | store a string value in global state

setParamString	:: String -> String -> IOSArrow b b
setParamString n v
    = perform (txt v >>> setParam n)

-- | read a string value from global state,
-- if parameter not set \"\" is returned

getParamString	:: String -> IOSArrow b String
getParamString n
    = xshow (getParam n)

-- | store an int value in global state

setParamInt	:: String -> Int -> IOSArrow b b
setParamInt n v
    = setParamString n (show v)

-- | read an int value from global state
-- 
-- example for reading trace level with default 0
--
-- > getParamInt 0 a_trace

getParamInt	:: Int -> String -> IOSArrow b Int
getParamInt def n
    = constA undefined
      >>> xshow (getParam n)
      >>> arr (\ x -> if null x then def else read x)

-- ------------------------------------------------------------

-- | reset global error variable

clearErrStatus	:: IOSArrow b b
clearErrStatus	= perform (constA 0 >>> setErrStatus)

-- | set global error variable

setErrStatus	:: IOSArrow Int XmlTree
setErrStatus	= arr show >>> mkText >>> setParam a_status

-- | read current global error status

getErrStatus	:: IOSArrow XmlTree Int
getErrStatus	= getParamInt 0 a_status

-- | raise the global error status level to that of the input tree
setErrMsgStatus	:: IOSArrow XmlTree XmlTree
setErrMsgStatus
    = perform ( getErrorLevel &&& getErrStatus
		>>>
		arr2 max
		>>>
		setErrStatus
	      )

-- | key for accessing error message handler in global state
a_errorMsgHandler	:: String
a_errorMsgHandler	= "error-message-handler"

-- | key for error message list variable in global state,
-- only used when errors are collected, and not issued imediately

a_errorList		:: String
a_errorList		= "error-list"

-- | set the error message handler, e.g issue, collect, ignore

setErrorMsgHandler	:: IOSArrow XmlTree XmlTree -> IOSArrow b b
setErrorMsgHandler hdl
    = perform ( constA hdl
		>>>
		setParamArrow a_errorMsgHandler
	      )

-- | apply the error message handler to a XML tree, possibly consisting of an error tree

errorMsgHandler		:: IOSArrow XmlTree XmlTree
errorMsgHandler
    = applyA (getParamArrow errorMsgStderr a_errorMsgHandler)

-- | error message handler for output to stderr
		  
errorMsgStderr		:: IOSArrow XmlTree XmlTree
errorMsgStderr
    = perform ( getErrorLevel &&& getErrorMsg
		>>>
		arr formatErrorMsg
		>>>
		arrIO (hPutStrLn stderr)
	      )
    where
    formatErrorMsg (level, msg)	= "\n" ++ errClass level ++ ": " ++ msg
    errClass l
	= fromMaybe "fatal error" . lookup l $ msgList
	  where
	  msgList	= [ (c_ok,	"no error")
			  , (c_warn,	"warning")
			  , (c_err,	"error")
			  , (c_fatal,	"fatal error")
			  ]

-- | error message handler for collecting errors

errorMsgCollect		:: IOSArrow XmlTree XmlTree
errorMsgCollect
    = IOSLA $ \ s x ->
      let
      XIOS al	= s
      errs	= lookupDef none a_errorList al
      errs'	= errs <+> constA x
      al'	= addEntry a_errorList errs' al
      in
      return (XIOS al', [x])

-- | error message handler for output to stderr and collecting

errorMsgStderrAndCollect	:: IOSArrow XmlTree XmlTree
errorMsgStderrAndCollect	= errorMsgStderr >>> errorMsgCollect

-- |
-- if error messages are collected by the error handler for
-- processing these messages by the calling application,
-- this arrow reads the stored messages and clears the error message store

getErrorMessages	:: IOSArrow b XmlTree
getErrorMessages
    = txt ""		-- undefined gives same result
      >>>
      getParam a_errorList
      >>>
      unsetParam a_errorList

-- ------------------------------------------------------------

-- |
-- filter error messages from input trees and issue errors

filterErrorMsg		:: IOSArrow XmlTree XmlTree
filterErrorMsg		= ( setErrMsgStatus >>> errorMsgHandler >>> none )
			  `when`
			  isError

-- | generate a warnig message

issueWarn	:: String -> IOSArrow b b
issueWarn msg	= perform (warn msg  >>> filterErrorMsg)

-- | generate an error message
issueErr	:: String -> IOSArrow b b
issueErr msg	= perform (err msg   >>> filterErrorMsg)

-- | generate a fatal error message, e.g. document not found

issueFatal	:: String -> IOSArrow b b
issueFatal msg	= perform (fatal msg >>> filterErrorMsg)

-- |
-- add the error level and the module where the error occured
-- to the attributes of a document root node and remove the children when level is greater or equal to 'c_err'.
-- called by 'setDocumentStatusFromSystemState' when the system state indicates an error

setDocumentStatus	:: Int -> String -> IOSArrow XmlTree XmlTree
setDocumentStatus level msg
    = ( addAttrl ( sattr a_status (show level)
		   <+>
		   sattr a_module msg
		 )
	>>>
	( if level >= c_err
	  then setChildren []
	  else this
	)
      )
      `when`
      isRoot

-- |
-- check whether the error level attribute in the system state
-- is set to error, in this case the children of the document root are
-- removed and the module name where the error occured and the error level are added as attributes with 'setDocumentStatus'
-- else nothing is changed

setDocumentStatusFromSystemState		:: String -> IOSArrow XmlTree XmlTree
setDocumentStatusFromSystemState msg
    = applyA ( getErrStatus
	       >>>
	       arr ( \ level -> if level <= c_warn
	                        then this
                                else setDocumentStatus level msg
		   )
	     )

-- |
-- check whether tree is a document root and the status attribute has a value less than 'c_err'

documentStatusOk	:: IOSArrow XmlTree XmlTree
documentStatusOk
    = isRoot
      >>>
      ( (getAttrValue a_status
	 >>>
	 isA (\ v -> null v || ((read v)::Int) <= c_warn)
	)
	`guards`
	this
      )

-- ------------------------------------------------------------

-- | set the base URI of a document, used e.g. for reading includes, e.g. external entities,
-- the input must be an absolute URI

setBaseURI		:: IOSArrow String String
setBaseURI
    = applyA (arr (setParamString transferURI))
      >>>
      traceString 2 (("setBaseURI: new base URI is " ++) . show)

-- | read the base URI from the globale state

getBaseURI		:: IOSArrow b String
getBaseURI
    = getParamString transferURI		-- try to find base uri in global parameter state
      >>>
      ( ( getDefaultBaseURI
	  >>>
	  setBaseURI		
	  >>>
	  getBaseURI
	)
	`when`
	isA null				-- set and get it, if not yet done
      )

-- | change the base URI with a possibly relative URI, can be used for
-- evaluating the xml:base attribute. returns the new absolute base URI
-- fails, if input is not parsable with parseURIReference
--
-- see also: 'setBaseURI', 'mkAbsURI'

changeBaseURI		:: IOSArrow String String
changeBaseURI
    = mkAbsURI >>> setBaseURI

-- | set the default base URI, if parameter is null, the system base (@ file:\/\/\/\<cwd\>\/ @) is used,
-- else the parameter, must be called before any document is read

setDefaultBaseURI	:: String -> IOSArrow b String
setDefaultBaseURI base
    = ( if null base
	then arrIO getDir
	else constA base
      )
      >>>
      perform ( mkText
		>>>
		setParam transferDefaultURI
	      )
    where
    getDir _ = do
	       cwd <- getCurrentDirectory
	       return ("file://" ++ cwd ++ "/")

-- | get the default base URI

getDefaultBaseURI	:: IOSArrow b String
getDefaultBaseURI
    = getParamString transferDefaultURI		-- try to find default uri in global parameter state
      >>>
      ( setDefaultBaseURI ""			-- set the default uri in  global parameter state
	>>>
	getDefaultBaseURI ) `when` isA null	-- when uri not yet set

-- ------------------------------------------------------------

-- | remember base uri, run an arrow and restore the base URI, used with external entity substitution

runInLocalURIContext	:: IOSArrow b c -> IOSArrow b c
runInLocalURIContext f
    = ( getBaseURI &&& this )
      >>>
      ( this *** listA f )
      >>>
      ( setBaseURI *** this )
      >>>
      arrL snd

-- ------------------------------------------------------------

-- | set the global trace level

setTraceLevel	:: Int -> IOSArrow b b
setTraceLevel lev
    = setParamInt a_trace lev

-- | read the global trace level

getTraceLevel	:: IOSArrow b Int
getTraceLevel
    = getParamInt 0 a_trace

-- | apply a trace arrow and issue message to stderr

trace		:: Int -> IOSArrow b String -> IOSArrow b b
trace level trc
    = perform ( trc
		>>>
		arrIO (hPutStrLn stderr)
	      )
      `when` ( getTraceLevel
	       >>>
	       isA (>= level)
	     )

-- | issue a string message as trace 
traceMsg	:: Int -> String -> IOSArrow b b
traceMsg level msg
    = perform ( trace level $
		constA ('-' : "- (" ++ show level ++ ") " ++ msg)
	      )

-- | issue the string input of an arrow
traceString	:: Int -> (String -> String) -> IOSArrow String String
traceString level f
    = perform (applyA (arr f >>> arr (traceMsg level)))

-- | issue the source representation of a document if trace level >= 3
traceSource	:: IOSArrow XmlTree XmlTree
traceSource 
    = trace 3 $
      xshow this

-- | issue the tree representation of a document if trace level >= 4
traceTree	:: IOSArrow XmlTree XmlTree
traceTree
    = trace 4 $
      xshow ( treeRepOfXmlDoc
	      >>>
	      addHeadlineToXmlDoc
	      >>>
	      getChildren
	    )

-- | trace a main computation step
-- issue a message when trace level >= 1, issue document source if level >= 3, issue tree when level is >= 4

traceDoc	:: String -> IOSArrow XmlTree XmlTree
traceDoc msg
    = traceMsg 1 msg
      >>>
      traceSource
      >>>
      traceTree

-- | trace the global state

traceState	:: IOSArrow b b
traceState
    = perform ( xshow ( (getAllParams >>. concat)
			>>>
			applyA (arr formatParam)
		      )
		>>>
		traceString 2 ("global state:\n" ++)
	      )
      where
      -- formatParam	:: (String, XmlTrees) -> IOSArrow b1 XmlTree
      formatParam (n, v)
	  = mkelem "param" [sattr "name" n] [arrL (const v)] <+> txt "\n"

-- ----------------------------------------------------------

-- | compute the absolut URI for a given URI and a base URI

expandURIString	:: String -> String -> Maybe String
expandURIString uri base
    = do
      base' <- parseURIReference base
      uri'  <- parseURIReference uri
      abs'  <- nonStrictRelativeTo uri' base'
      return $ show abs'

-- | arrow variant of 'expandURIString', fails if 'expandURIString' returns Nothing

expandURI		:: ArrowXml a => a (String, String) String
expandURI
    = arrL (maybeToList . uncurry expandURIString)

-- | arrow for expanding an input URI into an absolute URI using global base URI, fails if input is not a legal URI

mkAbsURI		:: IOSArrow String String
mkAbsURI
    = ( this &&& getBaseURI ) >>> expandURI

-- | arrow for selecting the scheme (protocol) of the URI, fails if input is not a legal URI.
--
-- See Network.URI for URI components

getSchemeFromURI	:: ArrowList a => a String String
getSchemeFromURI	= getPartFromURI scheme
    where
    scheme = init . uriScheme

-- | arrow for selecting the registered name (host) of the URI, fails if input is not a legal URI

getRegNameFromURI	:: ArrowList a => a String String
getRegNameFromURI	= getPartFromURI host
    where
    host = maybe "" uriRegName . uriAuthority

-- | arrow for selecting the port number of the URI without leading \':\', fails if input is not a legal URI

getPortFromURI		:: ArrowList a => a String String
getPortFromURI		= getPartFromURI port
    where
    port = dropWhile (==':') . maybe "" uriPort . uriAuthority

-- | arrow for selecting the user info of the URI without trailing \'\@\', fails if input is not a legal URI

getUserInfoFromURI		:: ArrowList a => a String String
getUserInfoFromURI		= getPartFromURI ui
    where
    ui = reverse . dropWhile (=='@') . reverse . maybe "" uriUserInfo . uriAuthority

-- | arrow for computing the path component of an URI, fails if input is not a legal URI

getPathFromURI		:: ArrowList a => a String String
getPathFromURI		= getPartFromURI uriPath

-- | arrow for computing the query component of an URI, fails if input is not a legal URI

getQueryFromURI		:: ArrowList a => a String String
getQueryFromURI		= getPartFromURI uriQuery

-- | arrow for computing the fragment component of an URI, fails if input is not a legal URI

getFragmentFromURI	:: ArrowList a => a String String
getFragmentFromURI	= getPartFromURI uriFragment

-- | arrow for computing the path component of an URI, fails if input is not a legal URI

getPartFromURI		:: ArrowList a => (URI -> String) -> a String String
getPartFromURI sel
    = arrL (maybeToList . getPart)
      where
      getPart s = do
		  uri <- parseURIReference s
		  return (sel uri)

-- ------------------------------------------------------------

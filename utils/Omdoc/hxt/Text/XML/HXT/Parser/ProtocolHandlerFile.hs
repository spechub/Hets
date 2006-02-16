-- ------------------------------------------------------------
--
-- protocol handler function for file protocol
-- implemented as filer
--
-- Version : $Id$

module Text.XML.HXT.Parser.ProtocolHandlerFile
    ( getFileContents
    )

where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.DOM.XmlState

import System.Directory
    ( doesFileExist
    , getPermissions
    , readable
    )

import Network.URI
    ( URI
    , path
    )

import System.IO
import System.IO.Error

-- ------------------------------------------------------------
--
-- the file protocol handler

getFileContents	:: URI -> XmlStateFilter a
getFileContents uri n
    = do
      trace 2 ("getFileContent: reading file " ++ show source)
      exists <- io $ doesFileExist source
      if exists
	 then do
	      perm <- io $ getPermissions source
	      if readable perm
		 then do
		      h <- io $ try ( openFile source ReadMode )
		      case h of
			     Left e
				 -> readErr ( "system error when reading file "
					      ++ show source
					      ++ ": "
					      ++ ioeGetErrorString e
					    )
			     Right h'
				 -> do
				    c <- io $ hGetContents h'
				    return ( ( addAttrInt transferStatus 200
					       .>
					       addAttr transferMessage "OK"
					       .>
					       replaceChildren (xtext c)
					     ) n
					   )

		 else readErr ("file " ++ show source ++ " not readable")
         else readErr ("file " ++ show source ++ " not found")
    where
    source	= path uri
    readErr msg	= addFatal msg n

-- ------------------------------------------------------------

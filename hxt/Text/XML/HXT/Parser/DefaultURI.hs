-- ------------------------------------------------------------
--
-- defaut uri computation
-- this routine is platform dependent
-- and must be exchanged when porting the toolbox e.g. to windows
--
-- Version : $Id$

module Text.XML.HXT.Parser.DefaultURI
    ( setDefaultURI
    )

where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.DOM.XmlState

import System.Directory
    ( getCurrentDirectory
    )

setDefaultURI	:: XState state ()
setDefaultURI
    = do
      wd <- io getCurrentDirectory
      setSysParam transferDefaultURI ("file://" ++ editCWD wd ++ "/")
    where
    -- under Windows getCurrentDirectory returns something like: "c:\path\to\file"
    -- backslaches are not allowed in URIs and paths must start with a /
    -- so this is transformed into "/c:/path/to/file"

    editCWD = addLeadingSlash . map backslash2slash

    addLeadingSlash s@('/' : _) = s
    addLeadingSlash s           = '/':s

    backslash2slash '\\' = '/'
    backslash2slash c    = c
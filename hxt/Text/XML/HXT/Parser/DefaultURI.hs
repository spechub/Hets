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
      setSysParam transferDefaultURI ("file://localhost" ++ wd ++ "/")


-- |
-- The arrow api
--
-- Version : $Id$
--
--
-- the application programming interface to the arrow modules of the Haskell XML Toolbox.
-- this module exports all important arrows for input, output, parsing, validating and transforming XML.
-- it also exports all basic datatypes and functions of the toolbox.
--

module Text.XML.HXT.Arrow
    ( module Control.Arrow.ListArrows

    , module Text.XML.HXT.DOM.XmlKeywords
    , module Text.XML.HXT.DOM.TypeDefs			-- XML types

    , module Text.XML.HXT.Parser.XmlOptions

    , module Text.XML.HXT.Arrow.XmlArrow
    , module Text.XML.HXT.Arrow.XmlIOStateArrow
    , module Text.XML.HXT.Arrow.XmlFilterInterface
    , module Text.XML.HXT.Arrow.GeneralEntitySubstitution
    , module Text.XML.HXT.Arrow.Namespace
    , module Text.XML.HXT.Arrow.DocumentInput
    , module Text.XML.HXT.Arrow.DocumentOutput
    , module Text.XML.HXT.Arrow.XmlStateFilterInterface
    , module Text.XML.HXT.Arrow.ReadDocument
    , module Text.XML.HXT.Arrow.WriteDocument
    )
where

import Control.Arrow.ListArrows			-- arrow classes

import Text.XML.HXT.DOM.XmlKeywords		-- constants
import Text.XML.HXT.DOM.TypeDefs		-- XML Tree types

import Text.XML.HXT.Parser.XmlOptions		-- input options

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.GeneralEntitySubstitution
import Text.XML.HXT.Arrow.Namespace
import Text.XML.HXT.Arrow.DocumentInput
import Text.XML.HXT.Arrow.DocumentOutput
import Text.XML.HXT.Arrow.XmlStateFilterInterface
import Text.XML.HXT.Arrow.ReadDocument
import Text.XML.HXT.Arrow.WriteDocument

-- ------------------------------------------------------------

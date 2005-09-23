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
    ( module Control.Arrow				-- arrow classes
    , module Control.Arrow.ArrowList
    , module Control.Arrow.ArrowIf
    , module Control.Arrow.ArrowState
    , module Control.Arrow.ArrowTree
    , module Control.Arrow.ArrowIO

    , module Control.Arrow.ListArrow			-- arrow types
    , module Control.Arrow.StateListArrow
    , module Control.Arrow.IOListArrow
    , module Control.Arrow.IOStateListArrow

    , module Text.XML.HXT.DOM.XmlKeywords
    , module Text.XML.HXT.DOM.TypeDefs			-- XML types

    , module Text.XML.HXT.Parser.XmlOptions

    , module Text.XML.HXT.Arrow.XmlArrow
    , module Text.XML.HXT.Arrow.XmlIOStateArrow
    , module Text.XML.HXT.Arrow.XmlFilterInterface
    , module Text.XML.HXT.Arrow.GeneralEntitySubstitution
    , module Text.XML.HXT.Arrow.DocumentInput
    , module Text.XML.HXT.Arrow.DocumentOutput
    , module Text.XML.HXT.Arrow.XmlStateFilterInterface
    )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowState
import Control.Arrow.ArrowTree
import Control.Arrow.ArrowIO

import Control.Arrow.ListArrow			-- arrow types
import Control.Arrow.StateListArrow
import Control.Arrow.IOListArrow
import Control.Arrow.IOStateListArrow

import Text.XML.HXT.DOM.XmlKeywords		-- constants
import Text.XML.HXT.DOM.TypeDefs		-- XML Tree types

import Text.XML.HXT.Parser.XmlOptions		-- input options

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
import Text.XML.HXT.Arrow.GeneralEntitySubstitution
import Text.XML.HXT.Arrow.DocumentInput
import Text.XML.HXT.Arrow.DocumentOutput
import Text.XML.HXT.Arrow.XmlStateFilterInterface

-- ------------------------------------------------------------


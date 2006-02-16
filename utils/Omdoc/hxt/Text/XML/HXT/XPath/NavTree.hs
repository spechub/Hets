-- |
-- Navigable tree structure which allow a program to traverse
-- for XPath expressions
-- copied and modified from HXML (<http://www.flightlab.com/~joe/hxml/>)
--

module Text.XML.HXT.XPath.NavTree
    ( module Text.XML.HXT.XPath.NavTree
    , module Data.NavTree
    )
where

import Data.NavTree

import Text.XML.HXT.DOM.XmlTreeTypes
    ( XNode(..) )

import Text.XML.HXT.DOM.XmlTreeFilter
    (isRoot)

import Data.Maybe
	
-- -----------------------------------------------------------------------------
-- functions for representing XPath axes. All axes except the namespace-axis are supported

ancestorAxis, ancestorOrSelfAxis, childAxis,
    descendantAxis, descendantOrSelfAxis,
    followingAxis, followingSiblingAxis, parentAxis,
    precedingAxis, precedingSiblingAxis, selfAxis
    :: NavTree a -> [NavTree a]


parentAxis		= maybeToList . upNT
ancestorAxis 		= \(NT _ u _ _) -> u		-- or: maybePlus upNT
ancestorOrSelfAxis	= \t@(NT _ u _ _) -> t:u	-- or: maybeStar upNT
childAxis		= maybe [] (maybeStar rightNT) . downNT
descendantAxis		= tail . preorderNT -- concatMap preorderNT . childAxis
descendantOrSelfAxis	= preorderNT
followingSiblingAxis	= maybePlus rightNT
precedingSiblingAxis	= maybePlus leftNT
selfAxis		= wrap  where wrap x = [x]

followingAxis = preorderNT     `o'` followingSiblingAxis `o'` ancestorOrSelfAxis
precedingAxis = revPreorderNT  `o'` precedingSiblingAxis `o'` ancestorOrSelfAxis


attributeAxis :: NavTree XNode -> [NavTree XNode]
attributeAxis t@(NT n@(NTree (XTag _ al) _) a _ _)
    | isRoot n == []    = foldr (\ attr -> ((NT attr (t:a) [] []):)) [] al
    | otherwise         = []
attributeAxis _ = []


 {- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

change an Xml-DGraph according to XmlDiff-data.
-}

module Static.ApplyXmlDiff where

import Common.XSimplePath

import Text.XML.Light

printXmlDiff :: Element -> String -> IO ()
printXmlDiff el diff = do
  ef <- getEffect el diff
  putStrLn $ show ef

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = changeXml el diff



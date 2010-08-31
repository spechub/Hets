{- |
Module      :  GUI.Glade.%s
Description :  Glade xmlstring for %s
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a string containing the xml data of the glade file for:
%s

This module is automatically created.
-}

module GUI.Glade.%s (get)
where

get :: (String, String)
get = ("%s", xmlString)

xmlString :: String
xmlString =

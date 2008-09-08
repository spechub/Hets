{- |
Module      :  GUI.Glade.%s
Description :  Glade xmlstring for %s
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

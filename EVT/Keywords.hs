{- |
Module      :  $Header$
Description :  CspCASL keywords to be used for parsing and printing
Copyright   :  (c) Andy Gimblett and Swansea University 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

String constants for CspCASL keywords to be used for parsing and
printing.

-}

module EVT.Keywords where 

-- | Keywords identifying beginning of eventdeclaration part.
event :: String
event = "event"

grd :: String
grd = "grd"

action :: String
action = "act"

assign:: String
assign = ":="

checkeq :: String
checkeq = "="

member :: String
member = ":"

thenaturalnumbers:: String
thenaturalnumbers = "thenats"


-- | starting EVT keywords
startKeywords :: [String]
startKeywords =
  [ event
  , grd
  , action]

-- | Reserved keywords specific to EVT.
evtKeywords :: [String]
evtKeywords = startKeywords ++
  [ assign, checkeq]

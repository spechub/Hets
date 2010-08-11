{- |
Module      :  $Header$
Description :  String constants for OWL keywords to be used for parsing
  and printing
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords to be used for parsing and printing

- all identifiers are mixed case (i.e. the keyword followed by a capital S)
-}

module OWL.Keywords where

keywords :: [String]
keywords =
  [ booleanS
  , dATAS
  , decimalS
  , digitsS
  , exactlyS
  , floatS
  , fractionS
  , functionalS
  , hasS
  , integerS
  , inverseS
  , lengthS
  , maxLengthS
  , maxS
  , minLengthS
  , minS
  , negativeIntegerS
  , nonNegativeIntegerS
  , nonPositiveIntegerS
  , oS
  , onlyS
  , onlysomeS
  , orS
  , patternS
  , positiveIntegerS
  , selfS
  , someS
  , thatS
  , universalS
  , valueS
  , xorS
  ]

booleanS :: String
booleanS = "boolean"

dATAS :: String
dATAS = "DATA"

decimalS :: String
decimalS = "decimal"

digitsS :: String
digitsS = "digits"

exactlyS :: String
exactlyS = "exactly"

floatS :: String
floatS = "float"

fractionS :: String
fractionS = "fraction"

functionalS :: String
functionalS = "Functional"

hasS :: String
hasS = "has"

integerS :: String
integerS = "integer"

inverseS :: String
inverseS = "inverse"

lengthS :: String
lengthS = "length"

maxLengthS :: String
maxLengthS = "maxLength"

maxS :: String
maxS = "max"

minLengthS :: String
minLengthS = "minLength"

minS :: String
minS = "min"

negativeIntegerS :: String
negativeIntegerS = "negativeInteger"

nonNegativeIntegerS :: String
nonNegativeIntegerS = "nonNegativeInteger"

nonPositiveIntegerS :: String
nonPositiveIntegerS = "nonPositiveInteger"

oS :: String
oS = "o"

onlyS :: String
onlyS = "only"

onlysomeS :: String
onlysomeS = "onlysome"

orS :: String
orS = "or"

patternS :: String
patternS = "pattern"

positiveIntegerS :: String
positiveIntegerS = "positiveInteger"

selfS :: String
selfS = "Self"

someS :: String
someS = "some"

thatS :: String
thatS = "that"

universalS :: String
universalS = "Universal"

valueS :: String
valueS = "value"

xorS :: String
xorS = "xor"

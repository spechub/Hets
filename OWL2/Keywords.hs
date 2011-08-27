{- |
Module      :  $Header$
Description :  String constants for OWL keywords to be used for parsing
  and printing
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords to be used for parsing and printing

- all identifiers are mixed case (i.e. the keyword followed by a capital S)
-}

module OWL2.Keywords where

keywords :: [String]
keywords =
  [ base64BinaryS
  , booleanS
  , byteS
  , dATAS
  , decimalS
  , digitsS
  , exactlyS
  , floatS
  , fractionS
  , functionalS
  , hasS
  , hexBinaryS
  , intS
  , integerS
  , inverseS
  , lengthS
  , longS
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
  , rationalS
  , realS
  , selfS
  , shortS
  , someS
  , thatS
  , rdfsLiteral
  , unsignedByteS
  , unsignedIntS
  , unsignedLongS
  , unsignedShortS
  , valueS
  , dateTimeS
  , dateTimeStampS
  , anyURI
  , xmlLiteral
  , ncNameS
  , nameS
  , nmTokenS
  , tokenS
  , languageS
  , normalizedStringS
  , xorS
  ]

base64BinaryS :: String
base64BinaryS = "base64Binary"

booleanS :: String
booleanS = "boolean"

byteS :: String
byteS = "byte"

dATAS :: String
dATAS = "DATA"

decimalS :: String
decimalS = "decimal"

doubleS :: String
doubleS = "double"

digitsS :: String
digitsS = "totalDigits"

exactlyS :: String
exactlyS = "exactly"

floatS :: String
floatS = "float"

fractionS :: String
fractionS = "fractionDigits"

functionalS :: String
functionalS = "Functional"

hasS :: String
hasS = "has"

hexBinaryS :: String
hexBinaryS = "hexBinary"

intS :: String
intS = "int"

integerS :: String
integerS = "integer"

inverseS :: String
inverseS = "inverse"

langRangeS :: String
langRangeS = "langRange"

lengthS :: String
lengthS = "length"

longS :: String
longS = "long"

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

rationalS :: String
rationalS = "rational"

realS :: String
realS = "real"

selfS :: String
selfS = "Self"

shortS :: String
shortS = "short"

someS :: String
someS = "some"

thatS :: String
thatS = "that"

rdfsLiteral :: String
rdfsLiteral = "Literal"

unsignedByteS :: String
unsignedByteS = "unsignedByte"

unsignedIntS :: String
unsignedIntS = "unsignedInt"

unsignedLongS :: String
unsignedLongS = "unsignedLongS"

unsignedShortS :: String
unsignedShortS = "unsignedShort"

valueS :: String
valueS = "value"

xorS :: String
xorS = "xor"

dateTimeS :: String
dateTimeS = "dateTime"

dateTimeStampS :: String
dateTimeStampS = "dateTimeStamp"

anyURI :: String
anyURI = "anyURI"

xmlLiteral :: String
xmlLiteral = "XMLLiteral"

ncNameS :: String
ncNameS = "NCName"

nameS :: String
nameS = "Name"

nmTokenS :: String
nmTokenS = "NMTOKEN"

tokenS :: String
tokenS = "token"

languageS :: String
languageS = "language"

normalizedStringS :: String
normalizedStringS = "normalizedString"

thing :: String
thing = "Thing"

nothing :: String
nothing = "Nothing"

topObjProp :: String
topObjProp = "topObjectProperty"

bottomObjProp :: String
bottomObjProp = "bottomObjectProperty"

topDataProp :: String
topDataProp = "topDataProperty"

bottomDataProp :: String
bottomDataProp = "bottomDataProperty"

label :: String
label = "label"

comment :: String
comment = "comment"

seeAlso :: String
seeAlso = "seeAlso"

isDefinedBy :: String
isDefinedBy = "isDefinedBy"

deprecated :: String
deprecated = "deprecated"

versionInfo :: String
versionInfo = "versionInfo"

priorVersion :: String
priorVersion = "priorVersion"

backwardCompatibleWith :: String
backwardCompatibleWith = "backwardCompatibleWith"

incompatibleWith :: String
incompatibleWith = "incompatibleWith"

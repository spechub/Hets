{- |
Module      :  ./OWL2/Keywords.hs
Description :  OWL reserved keywords
  and printing
Copyright   :  (c) Christian Maeder DFKI Bremen 2008, Felix Mance, 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords to be used for parsing and printing
plus owl, xsd, rdf and rdfs reserved keywords. All identifiers are mixed case
-}

module OWL2.Keywords where

import Common.Keywords

keywords :: [String]
keywords =
  [ digitsS
  , exactlyS
  , fractionS
  , functionalS
  , hasS
  , inverseS
  , lengthS
  , maxLengthS
  , maxS
  , minLengthS
  , minS
  , oS
  , onlyS
  , onlysomeS
  , orS
  , patternS
  , selfS
  , someS
  , thatS
  , valueS
  , xorS
  ] ++ datatypeKeys

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

inverseFunctionalS :: String
inverseFunctionalS = "InverseFunctional"

reflexiveS :: String
reflexiveS = "Reflexive"

irreflexiveS :: String
irreflexiveS = "Irreflexive"

symmetricS :: String
symmetricS = "Symmetric"

asymmetricS :: String
asymmetricS = "Asymmetric"

antisymmetricS :: String
antisymmetricS = "Antisymmetric"

transitiveS :: String
transitiveS = "Transitive"

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

thingS :: String
thingS = "Thing"

nothingS :: String
nothingS = "Nothing"

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

implied :: String
implied = "Implied"

predefClass :: [String]
predefClass = [thingS, nothingS]

predefObjProp :: [String]
predefObjProp = [topObjProp, bottomObjProp]

predefDataProp :: [String]
predefDataProp = [topDataProp, bottomDataProp]

predefRDFSAnnoProps :: [String]
predefRDFSAnnoProps = [label, comment, seeAlso, isDefinedBy]

predefOWLAnnoProps :: [String]
predefOWLAnnoProps = [deprecated, versionInfo, priorVersion,
    backwardCompatibleWith, incompatibleWith, implied]

xsdNumbers :: [String]
xsdNumbers = [integerS, negativeIntegerS, nonNegativeIntegerS,
    nonPositiveIntegerS, positiveIntegerS, decimalS, doubleS, floatS,
    longS, intS, shortS, byteS, unsignedLongS, unsignedIntS, unsignedShortS,
    unsignedByteS]

owlNumbers :: [String]
owlNumbers = [realS, rationalS]

xsdStrings :: [String]
xsdStrings = [stringS, ncNameS, "QName", nameS, nmTokenS, "NMTOKENS", tokenS
  , languageS, normalizedStringS, "NOTATION", "ENTITY", "ENTITIES"
  , "ID", "IDREF", "IDREFS" ]

xsdKeys :: [String]
xsdKeys = [booleanS, dATAS, hexBinaryS, base64BinaryS, "date", "time"
  , "gYearMonth", "gYear", "gMonthDay", "gDay", "gMonth", "duration"
  , dateTimeS, dateTimeStampS, anyURI] ++ xsdNumbers ++ xsdStrings

nonXSDKeys :: [String]
nonXSDKeys = owlNumbers ++ [xmlLiteral, rdfsLiteral]

datatypeKeys :: [String]
datatypeKeys = xsdKeys ++ nonXSDKeys

data DatatypeFacet =
    LENGTH
  | MINLENGTH
  | MAXLENGTH
  | PATTERN
  | LANGRANGE
  | MININCLUSIVE
  | MINEXCLUSIVE
  | MAXINCLUSIVE
  | MAXEXCLUSIVE
  | TOTALDIGITS
  | FRACTIONDIGITS
    deriving (Show, Eq, Ord)

-- Converts a facet to string but in contrast to @showFacet@ uses text
-- instead of signs. E.g. "minInclusive" instead of "<="
showFacetAsText :: DatatypeFacet -> String
showFacetAsText LENGTH = lengthS
showFacetAsText MINLENGTH = minLengthS
showFacetAsText MAXLENGTH = maxLengthS
showFacetAsText PATTERN = patternS
showFacetAsText LANGRANGE = langRangeS
showFacetAsText MININCLUSIVE = minInclusiveS
showFacetAsText MINEXCLUSIVE = minExclusiveS
showFacetAsText MAXINCLUSIVE = maxInclusiveS
showFacetAsText MAXEXCLUSIVE = maxExclusiveS
showFacetAsText TOTALDIGITS = digitsS
showFacetAsText FRACTIONDIGITS = fractionS

showFacet :: DatatypeFacet -> String
showFacet df = case df of
    LENGTH -> lengthS
    MINLENGTH -> minLengthS
    MAXLENGTH -> maxLengthS
    PATTERN -> patternS
    LANGRANGE -> langRangeS
    MININCLUSIVE -> lessEq
    MINEXCLUSIVE -> lessS
    MAXINCLUSIVE -> greaterEq
    MAXEXCLUSIVE -> greaterS
    TOTALDIGITS -> digitsS
    FRACTIONDIGITS -> fractionS

facetList :: [DatatypeFacet]
facetList = [LENGTH, MINLENGTH, MAXLENGTH, PATTERN, LANGRANGE, MININCLUSIVE,
    MINEXCLUSIVE, MAXINCLUSIVE, MAXEXCLUSIVE, TOTALDIGITS, FRACTIONDIGITS]

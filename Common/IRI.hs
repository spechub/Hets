{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/IRI.hs
Copyright   :  (c) DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <eugenk@informatik.uni-bremen.de>
Stability   :  provisional
Portability :  portable

This module defines functions for handling IRIs.  It was adopted
from the Network.URI module by Graham Klyne, but is extended to IRI
support [2] and CURIE [3].

Four methods are provided for parsing different
kinds of IRI string (as noted in [1], [2]):
'parseIRI'
'parseIRIReference'


An additional method is provided for parsing an abbreviated IRI according to
[3]: 'parseIRICurie'

Additionally, classification of full, abbreviated and simple IRI is provided.

The abbreviated syntaxes [3] provide three different kinds of IRI.

References

(1) <http://www.ietf.org/rfc/rfc3986.txt>

(2) <http://www.ietf.org/rfc/rfc3987.txt>

(3) <http://www.w3.org/TR/rdfa-core/#s_curies>

-}

module Common.IRI
    ( IRI (..)
    , IRIAuth (IRIAuth)
    , nullIRI
    , iriToStringUnsecure
    , iriToStringShortUnsecure
    , hasFullIRI
    , isSimple
    , addSuffixToIRI

    -- * Parsing
    , iri
    , angles
    , iriCurie
    , compoundIriCurie  
    , parseCurie
    , parseIRICurie
    , parseIRIReference
    , parseIRI
    , ncname

    , expandCurie
    , relativeTo
    , relativeFrom

    -- * Conversion
    , simpleIdToIRI
    , deleteQuery
    , setAngles
   
    -- * methods from OWL2.AS
    , isNullIRI
    , iRIRange
    , showIRI
    , showIRIU
    , showIRII
    , dummyIRI
    , mkIRI
    , idToIRI  
    , setPrefix
    ) where

import Text.ParserCombinators.Parsec

import Data.Char
import Data.Data
import Data.Ord (comparing)
import Data.Map as Map (Map, lookup)
import Data.Maybe
import Data.List
import qualified Data.Map as Map

import Control.Monad (when)

import OWL2.ColonKeywords
import OWL2.Keywords

import Common.Id as Id
import Common.Lexer
import Common.Parsec
import Common.Percent
import Common.Token (mixId, comps)

-- * The IRI datatype

{- | Represents a general universal resource identifier using
its component parts.

For example, for the (full) IRI

>   foo://anonymous@www.haskell.org:42/ghc?query#frag

or the abbreviated IRI

>   prefix:iriPath?iriQuery#iriFragment

or the simple IRI

>  iriPath
-}



data IRI = IRI
    { iriScheme :: String         -- ^ @foo:@
    , iriAuthority :: Maybe IRIAuth -- ^ @\/\/anonymous\@www.haskell.org:42@
    , iriPath :: Id               -- ^ local part @\/ghc@
    , iriQuery :: String          -- ^ @?query@
    , iriFragment :: String       -- ^ @#frag@
    , prefixName :: String        -- ^ @prefix@
    , isAbbrev :: Bool            -- ^ is the IRI a CURIE or not?
    , isBlankNode :: Bool         -- ^ is the IRI a blank node?                   
    , hasAngles :: Bool           -- ^ IRI in angle brackets
    , iriPos :: Range             -- ^ position
    } deriving (Typeable, Data)

-- | Type for authority value within a IRI
data IRIAuth = IRIAuth
    { iriUserInfo :: String       -- ^ @anonymous\@@
    , iriRegName :: String        -- ^ @www.haskell.org@
    , iriPort :: String           -- ^ @:42@
    } deriving (Eq, Ord, Show, Typeable, Data)

-- | Blank IRI
nullIRI :: IRI
nullIRI = IRI
    { iriScheme = ""
    , iriAuthority = Nothing
    , iriPath = mkId []
    , iriQuery = ""
    , iriFragment = ""
    , prefixName = ""
    , isAbbrev = False
    , isBlankNode = False
    , hasAngles = False
    , iriPos = nullRange
    }

-- | special show function for Ids within IRIs
showIRIId :: Id -> String
showIRIId = show -- todo: to be refined.
-- @Till: do we need to show Ids differently within IRIs?

-- | do we have a full (possibly expanded) IRI (i.e. for comparisons)
hasFullIRI :: IRI -> Bool
hasFullIRI i = not . null $ iriScheme i ++ (show $ iriPath i)

{- | do we have a simple IRI that is a (possibly expanded) abbreviated IRI
without prefix -}
isSimple :: IRI -> Bool
isSimple i = null (prefixName i) && isAbbrev i

{- IRI as instance of Show.  Note that for security reasons, the default
behaviour should suppress any iuserinfo field (see RFC3986, section 7.5).
But we don't do this since we use iriToStringUnsecure all over the place
anyway. -}
instance Show IRI where
    showsPrec _ = iriToString id

-- equal iff expansion is equal or abbreviation is equal
instance Eq IRI where
  (==) i j = compare i j == EQ

-- compares full/expanded IRI (if expanded) or abbreviated part if not expanded
instance Ord IRI where
  compare i k = case (hasFullIRI i, hasFullIRI k) of
    (False, False) -> comparing
      (\ j -> (prefixName j, iriPath j, iriQuery j, iriFragment j))
      i k
    _ -> comparing (\ j ->
      (iriScheme j, iriAuthority j, iriPath j,
       iriQuery j, iriFragment j)) i k

-- |converts IRI to String of expanded form. if available. Also showing Auth
iriToStringUnsecure :: IRI -> String
iriToStringUnsecure i = iriToString id i ""

{- |converts IRI to String of abbreviated form. if available.
Also showing Auth info. -}
iriToStringShortUnsecure :: IRI -> String
iriToStringShortUnsecure i = iriToStringShort id i ""

instance GetRange IRI where
    getRange = iriPos

-- | Converts a Simple_ID to an IRI
simpleIdToIRI :: SIMPLE_ID -> IRI
simpleIdToIRI sid = nullIRI { iriPath = simpleIdToId sid
                            , iriPos = tokPos sid
                            , isAbbrev = True
                            }

-- * new functions for OWL.AS
-- | do we have a nullIRI
isNullIRI :: IRI -> Bool
isNullIRI i = i == nullIRI

-- | set the Range attribute of IRIs
setIRIRange :: Range -> IRI -> IRI
setIRIRange r i = i { iriPos = r }

-- | checks if a string (bound to be localPart of an IRI) contains \":\/\/\"
cssIRI :: String -> String
cssIRI i 
  | isInfixOf "://" i = "Full"
  | otherwise = "Abbreviated"

iRIRange :: IRI -> [Pos]
iRIRange i = let Range rs = iriPos i in case rs of
  [p] -> let
    p0 = if hasFullIRI i then Id.incSourceColumn p (-1) else p
    in tokenRange $ Token (showIRI i) $ Range [p0]
  _ -> rs

showIRI :: IRI -> String
showIRI i 
  | hasFullIRI i = showIRII i
  | otherwise = showIRIU i


-- | show IRI as abbreviated
showIRIU :: IRI -> String
showIRIU i
  | hasFullIRI i && not (isAbbrev i) = showIRII i
  | not $ null $ iriQuery i = tail $ iriQuery i
  | otherwise = showIRIAbbrev i

showIRIAbbrev :: IRI -> String
showIRIAbbrev i = iriToStringAbbrev i ""
 -- don't duplicate code

-- | show IRI in angle brackets as full IRI
showIRII :: IRI -> String
showIRII i = iriToStringFull id i ""
  -- this should behave like show, and there we use id
  
dummyIRI :: IRI
dummyIRI = nullIRI { 
       iriScheme = "http"
     , iriAuthority = Just IRIAuth
                       { iriUserInfo = ""
                       , iriRegName = "hets.eu"
                       , iriPort = "" }
     , iriPath = stringToId "/ontology/unamed"
    }

mkIRI :: String -> IRI
mkIRI = simpleIdToIRI. mkSimpleId

idToIRI :: Id -> IRI
idToIRI i =  nullIRI { iriScheme = ""
                     , iriAuthority = Nothing
                     , iriPath = i
                     , isAbbrev = True
                     }

setPrefix :: String -> IRI -> IRI
setPrefix s i = i{prefixName = s}

-- * Parse an IRI

{- | Turn a string containing an RFC3987 IRI into an 'IRI'.
Returns 'Nothing' if the string is not a valid IRI;
(an absolute IRI with optional fragment identifier). -}
parseIRI :: String -> Maybe IRI
parseIRI s = parseIRIAny iri s

{- | Parse a IRI reference to an 'IRI' value.
Returns 'Nothing' if the string is not a valid IRI reference.
(an absolute or relative IRI with optional fragment identifier). -}
parseIRIReference :: String -> Maybe IRI
parseIRIReference s = parseIRIAny iriReference s

-- | Turn a string containing a CURIE into an 'IRI'
parseCurie :: String -> Maybe IRI
parseCurie s = parseIRIAny curie s

{- | Turn a string containing an IRI or a CURIE into an 'IRI'.
Returns 'Nothing' if the string is not a valid IRI;
(an absolute IRI enclosed in '<' and '>' with optional fragment identifier
or a CURIE). -}
parseIRICurie :: String -> Maybe IRI
parseIRICurie = parseIRIAny iriCurie

-- Helper function for turning a string into a IRI
parseIRIAny :: IRIParser () IRI -> String -> Maybe IRI
parseIRIAny parser iristr = case parse (parser << eof) "" iristr of
        Left _ -> Nothing
        Right u -> Just u { iriPos = nullRange }

-- * IRI parser body based on Parsec elements and combinators

-- Parser parser type. Currently:
type IRIParser st a = GenParser Char st a

-- RFC3986, section 2.1

-- | Parse and return a 'pct-encoded' sequence
escaped :: IRIParser st String
escaped = char '%' <:> hexDigit <:> single hexDigit

-- RFC3986, section 2.2

subDelims :: IRIParser st String
subDelims = single $ oneOf subDelim

-- RFC3986, section 2.3

{- |Returns 'True' if the character is an \"unreserved\" character in
a IRI.  These characters do not need to be escaped in a IRI.  The
only characters allowed in a IRI are either \"reserved\",
\"unreserved\", or an escape sequence (@%@ followed by two hex digits). -}
isIUnreserved :: Char -> Bool
isIUnreserved c = isUnreserved c || isUcsChar c

iunreservedChar :: IRIParser st String
iunreservedChar = single $ satisfy isIUnreserved

iriWithPos :: IRIParser st IRI -> IRIParser st IRI
iriWithPos parser = do
  p <- getPos
  i <- parser
  q <- getPos
  return $ i {iriPos = appRange (Range [p, q]) $ iriPos i}


-- BEGIN CURIE

-- | Parses an IRI reference enclosed in '<', '>' or a CURIE
iriCurie :: IRIParser st IRI
iriCurie = angles iri <|> curie 

compoundIriCurie :: IRIParser st IRI
compoundIriCurie = angles iri <|> compoundCurie 

angles :: IRIParser st IRI -> IRIParser st IRI
angles p = char '<' >> fmap (\ i -> i { hasAngles = True }) p << char '>'

-- | Parses a CURIE possibly followed by components of a compound Id
compoundCurie :: IRIParser st IRI
compoundCurie = do
      i <- curie
      (c, p) <- option ([], nullRange) (comps ([], []))
      return i { iriPath = addComponents (iriPath i) (c,p),
                 isBlankNode = prefixName i == "_" }

-- | Parses a CURIE <http://www.w3.org/TR/rdfa-core/#s_curies>
curie :: IRIParser st IRI
curie = iriWithPos $ do
    pn <- try (do
        n <- ncname
        c <- string ":"
        return $ n ++ c
      )
    i <- reference
    return i { prefixName = pn }
  <|> referenceAux False

reference :: IRIParser st IRI
reference = referenceAux True

dolChar :: IRIParser st String
dolChar = ucharAux True "@:"

referenceAux :: Bool -> IRIParser st IRI
referenceAux allowEmpty = iriWithPos $ do
  up <- option "" (single $ char '/')
        <++> option "" ((dolChar <|> count 1 digit) <++>
                        flat (many $ ucharAux True "@:/.-"))
  uq <- option "" uiquery
  uf <- (if allowEmpty || not (null up) || not (null uq)
         then option "" else id) uifragment
  let iri = nullIRI
          { iriPath = stringToId up
          , iriQuery = uq
          , iriFragment = uf
          , isAbbrev = True  
          }
  return iri
  
{- | Prefix part of CURIE in @prefix_part:reference@
  <http://www.w3.org/TR/2009/REC-xml-names-20091208/#NT-NCName> -}
ncname :: GenParser Char st String
ncname = nameStartChar <:> many nameChar

nameStartChar :: GenParser Char st Char
nameStartChar = satisfy nameStartCharP

nameChar :: GenParser Char st Char
nameChar = satisfy nameCharP

{- NOTE: Usually ':' is allowed. Here, only ncname uses nameStartChar, however.
Thus we disallow ':' -}
nameStartCharP :: Char -> Bool
nameStartCharP c =
  (c == '_') ||       -- W3C: (c `elem` ":_") ||
  pnCharsBaseP c

nameCharP :: Char -> Bool
nameCharP c = nameStartCharP c || c `elem` "-." || pnCharsPAux c

-- END CURIE

-- BEGIN SPARQL

{- http://www.w3.org/TR/2008/REC-rdf-sparql-query-20080115/
Section 4.1 -}

pnCharsBaseP :: Char -> Bool
pnCharsBaseP c =
  let n = ord c in
  isAlphaChar c ||
  (0x00C0 <= n && n <= 0x00D6) ||
  (0x00D8 <= n && n <= 0x00F6) ||
  (0x00F8 <= n && n <= 0x02FF) ||
  (0x0370 <= n && n <= 0x037D) ||
  (0x037F <= n && n <= 0x1FFF) ||
  (0x200C <= n && n <= 0x200D) ||
  (0x2070 <= n && n <= 0x218F) ||
  (0x2C00 <= n && n <= 0x2FEF) ||
  (0x3001 <= n && n <= 0xD7FF) ||
  (0xF900 <= n && n <= 0xFDCF) ||
  (0xFDF0 <= n && n <= 0xFFFD) ||
  (0x10000 <= n && n <= 0xEFFFF)

pnCharsPAux :: Char -> Bool
pnCharsPAux c =
  let n = ord c in
  isDigit c ||
  (n == 0x00B7) ||
  (0x0300 <= n && n <= 0x036F) ||
  (0x203F <= n && n <= 0x2040)

-- RFC3987, section 2.2

-- IRI         = scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]

{- ihier-part   = "//" iauthority ipath-abempty
/ ipath-absolute
/ ipath-rootless
/ ipath-empty -}

iri :: IRIParser st IRI
iri = iriWithPos $ do
  us <- try uscheme
  (ua, up) <- ihierPart
  uq <- option "" uiquery
  uf <- option "" uifragment
  return nullIRI
            { iriScheme = us
            , iriAuthority = ua
            , iriPath = up
            , iriQuery = uq
            , iriFragment = uf
            }

ihierPart :: IRIParser st (Maybe IRIAuth, Id)
ihierPart = ihierOrIrelativePart
    <|> fmap (\ s -> (Nothing, s)) ihierPartNoAuth

ihierOrIrelativePart :: IRIParser st (Maybe IRIAuth, Id)
ihierOrIrelativePart =
  try (string "//") >> pair uiauthority ipathAbEmpty

ihierPartNoAuth :: IRIParser st Id
ihierPartNoAuth = ipathAbs <|> ipathRootLessId <|> (return $ stringToId "")

-- RFC3986, section 3.1

uscheme :: IRIParser st String
uscheme = satisfy isAlphaChar <:> many (satisfy isSchemeChar) <++> string ":"

-- RFC3987, section 2.2

uiauthority :: IRIParser st (Maybe IRIAuth)
uiauthority = do
  uu <- option "" (try iuserinfo)
  uh <- ihost
  up <- option "" port
  return $ Just IRIAuth
            { iriUserInfo = uu
            , iriRegName = uh
            , iriPort = up
            }

-- RFC3987, section 2.2

iuserinfo :: IRIParser st String
iuserinfo = flat (many $ uchar ";:&=+$,") <++> string "@"

-- RFC3987, section 2.2

ihost :: IRIParser st String
ihost = ipLiteral <|> try ipv4address <|> iregName

ipLiteral :: IRIParser st String
ipLiteral = char '[' <:> (ipv6address <|> ipvFuture) <++> string "]"
    <?> "IP address literal"

ipvFuture :: IRIParser st String
ipvFuture = char 'v' <:> hexDigit <:> char '.'
    <:> many1 (satisfy isIpvFutureChar)

isIpvFutureChar :: Char -> Bool
isIpvFutureChar c = isUnreserved c || elem c (':' : subDelim)

ipv6address :: IRIParser st String
ipv6address = do
    hs <- countMinMax 0 7 h4c
    fmap (concat hs ++) $ case length hs of
      7 -> h4 <|> string ":"
      6 -> ipv4address <|> char ':' <:> (h4 <|> return "")
      0 -> string "::" <++> ipv6rest 7
      n -> char ':' <:> ipv6rest (7 - n)
  <?> "IPv6 address"

ipv6rest :: Int -> IRIParser st String
ipv6rest m = do
    fs <- countMinMax 0 (m - 1) h4c
    fmap (concat fs ++) $ if null fs then
       ipv4address <|> h4 <|> return ""
       else if length fs == m - 1 then h4 else
        ipv4address <|> h4

h4c :: IRIParser st String
h4c = try $ h4 <++> string ":"

h4 :: IRIParser st String
h4 = countMinMax 1 4 hexDigit

ipv4address :: IRIParser st String
ipv4address = try (decOctet <++> string "."
    <++> decOctet) <++> string "."
    <++> decOctet <++> string "."
    <++> decOctet

decOctet :: IRIParser st String
decOctet = do
  a1 <- countMinMax 1 3 digit
  if (read a1 :: Int) > 255 then
            fail "Decimal octet value too large"
          else
            return a1

iregName :: IRIParser st String
iregName =
    flat (countMinMax 0 255 $ iunreservedChar <|> escaped <|> subDelims)
    <?> "Registered name"

-- RFC3986, section 3.2.3

port :: IRIParser st String
port = char ':' <:> many digit

-- RFC3987, section 2.2

{- ipath          = ipath-abempty   ; begins with "/" or is empty
/ ipath-absolute  ; begins with "/" but not "//"
/ ipath-noscheme  ; begins with a non-colon isegment
/ ipath-rootless  ; begins with a isegment
/ ipath-empty     ; zero characters -}

{- ipath-abempty  = *( "/" iisegment )
ipath-absolute = "/" [ iisegment-nz *( "/" iisegment ) ]
ipath-noscheme = iisegment-nz-nc *( "/" iisegment )
ipath-rootless = iisegment-nz *( "/" iisegment )
ipath-empty    = 0<iipchar> -}

{- iisegment       = *iipchar
iisegment-nz    = 1*iipchar
iisegment-nz-nc = 1*( iunreserved / pct-encoded / sub-delims
/ "@" )
; non-zero-length isegment without any colon ":" -}

{- iipchar         = iunreserved / pct-encoded / sub-delims / ":"
/ "@" -}

idParser :: IRIParser st Id
idParser = mixId ([],[]) ([],[]) 

ipathAbEmpty :: IRIParser st Id
ipathAbEmpty = do
  s <- flat $ many slashIsegment
  return $ stringToId s

ipathAbEmpty1 :: Bool -> IRIParser st Id
ipathAbEmpty1 slash = do
  when slash $ do char '/'; return ()
  si <- isegmentorId "/"
  case si of
    Left s ->     do char '/'
                     i <- ipathAbEmpty1 False
                     return $ prependString s i
              <|> do return $ stringToId ""  
    Right i -> return i

isegmentorId :: String -> IRIParser st (Either String Id)
isegmentorId lead =
      do s <- isegment
         return (Left ('/':s))
--  <|> do id <- idParser
--         return (Right (prependString "/" id))
  
ipathAbs :: IRIParser st Id
ipathAbs = do
  s <- char '/' <:> option "" ipathRootLess
  return $ stringToId s

ipathRootLessId :: IRIParser st Id
ipathRootLessId = do
  s <- ipathRootLess
  return $ stringToId s

ipathRootLess :: IRIParser st String
ipathRootLess = flat $ isegmentNz <:> many slashIsegment

ipathNoScheme :: IRIParser st Id
ipathNoScheme =  do
  s <- flat $ isegmentNzc <:> many slashIsegment
  return $ stringToId s

slashIsegment :: IRIParser st String
slashIsegment = char '/' <:> isegment

isegment :: IRIParser st String
isegment = flat $ many ipchar

isegmentNz :: IRIParser st String
isegmentNz = flat $ many1 ipchar

isegmentNzc :: IRIParser st String
isegmentNzc = flat . many1 $ uchar "@"

ipchar :: IRIParser st String
ipchar = uchar ":@"

uchar :: String -> IRIParser st String
uchar = ucharAux False

-- helper function for ipchar and friends
ucharAux :: Bool -> String -> IRIParser st String
ucharAux dolCurie extras =
        iunreservedChar
    <|> escaped
    <|> single (oneOf $ extras ++ if dolCurie then dolDelim else subDelim)

-- RFC3987, section 2.2

uiquery :: IRIParser st String
uiquery = char '?' <:> flat (many iqueryPart)

iqueryPart :: IRIParser st String
iqueryPart = many1 iprivate <|> uchar ":@/?"

-- RFC3987, section 2.2

uifragment :: IRIParser st String
uifragment = char '#' <:> flat (many $ uchar ":@/?")

-- Reference, Relative and Absolute IRI forms

-- RFC3987, section 2.2

iriReference :: IRIParser st IRI
iriReference = iri <|> irelativeRef

-- RFC3987, section 2.2

-- irelative-ref  = irelative-part [ "?" iquery ] [ "#" ifragment ]

{- irelative-part = "//" iauthority ipath-abempty
/ ipath-absolute -}

irelativeRef :: IRIParser st IRI
irelativeRef = iriWithPos $ do
  notMatching uscheme
  (ua, up) <- irelativePart
  uq <- option "" uiquery
  uf <- option "" uifragment
  return nullIRI
            { iriAuthority = ua
            , iriPath = up
            , iriQuery = uq
            , iriFragment = uf
            }

irelativePart :: IRIParser st (Maybe IRIAuth, Id)
irelativePart = ihierOrIrelativePart
  <|> fmap (\ s -> (Nothing, s)) (ipathAbs <|> ipathNoScheme <|> return (stringToId ""))

-- RFC3987, section 2.2 omitted absoluteIRI

-- Imports from RFC 2234

    {- NOTE: can't use isAlphaNum etc. because these deal with ISO 8859
    (and possibly Unicode!) chars.
    [[[Above was a comment originally in GHC Network/IRI.hs:
    when IRIs are introduced then most codepoints above 128(?) should
    be treated as unreserved, and higher codepoints for letters should
    certainly be allowed.
    ]]] -}

isAlphaChar :: Char -> Bool
isAlphaChar c = isAlpha c && isAscii c

isAlphaNumChar :: Char -> Bool
isAlphaNumChar c = isAlphaNum c && isAscii c

isSchemeChar :: Char -> Bool
isSchemeChar c = isAlphaNumChar c || c `elem` "+-."

isUcsChar :: Char -> Bool
isUcsChar c =
  let n = ord c
  in (0xA0 <= n && n <= 0xD7FF) ||
     (0xF900 <= n && n <= 0xFDCF) ||
     (0xFDF0 <= n && n <= 0xFFEF) ||
     (0x10000 <= n && n <= 0x1FFFD) ||
     (0x20000 <= n && n <= 0x2FFFD) ||
     (0x30000 <= n && n <= 0x3FFFD) ||
     (0x40000 <= n && n <= 0x4FFFD) ||
     (0x50000 <= n && n <= 0x5FFFD) ||
     (0x60000 <= n && n <= 0x6FFFD) ||
     (0x70000 <= n && n <= 0x7FFFD) ||
     (0x80000 <= n && n <= 0x8FFFD) ||
     (0x90000 <= n && n <= 0x9FFFD) ||
     (0xA0000 <= n && n <= 0xAFFFD) ||
     (0xB0000 <= n && n <= 0xBFFFD) ||
     (0xC0000 <= n && n <= 0xCFFFD) ||
     (0xD0000 <= n && n <= 0xDFFFD) ||
     (0xE1000 <= n && n <= 0xEFFFD) ||
     -- The following line is a custom extension. It is *not* part of the IRI
     -- standard, but necessary for the TPTP library (all THF examples) to
     -- work:
     c == '^'

isIprivate :: Char -> Bool
isIprivate c =
  let n = ord c
  in (0xE000 <= n && n <= 0xF8FF) ||
     (0xF000 <= n && n <= 0xFFFD) ||
     (0x100000 <= n && n <= 0x10FFFD)

iprivate :: IRIParser st Char
iprivate = satisfy isIprivate

-- Additional parser combinators for common patterns

countMinMax :: Int -> Int -> GenParser t s a -> GenParser t s [a]
countMinMax m n p | m > 0 = p <:> countMinMax (m - 1) (n - 1) p
countMinMax _ n _ | n <= 0 = return []
countMinMax _ n p = option [] $ p <:> countMinMax 0 (n - 1) p

notMatching :: Show a => GenParser tok st a -> GenParser tok st ()
notMatching p = do
    a <- try p
    unexpected (show a)
 <|> return ()

-- * Reconstruct a IRI string


{- | Turn an 'IRI' into a string.
Uses a supplied function to map the iuserinfo part of the IRI.
The Show instance for IRI uses a mapping that hides any password
that may be present in the IRI.  Use this function with argument @id@
to preserve the password in the formatted output. -}
iriToString :: (String -> String) -> IRI -> ShowS
iriToString iuserinfomap i
  | hasFullIRI i = iriToStringFull iuserinfomap i
  | otherwise = iriToStringAbbrev i

iriToStringShort :: (String -> String) -> IRI -> ShowS
iriToStringShort iuserinfomap i
  | hasFullIRI i && not (isAbbrev i) = iriToStringFull iuserinfomap i
  | not $ null $ iriQuery i = tail . (iriQuery i ++)
  | otherwise = iriToStringAbbrev i

iriToStringFull :: (String -> String) -> IRI -> ShowS
iriToStringFull iuserinfomap (IRI { iriScheme = scheme
                                  , iriAuthority = authority
                                  , iriPath = path
                                  , iriQuery = query
                                  , iriFragment = fragment
                                  , hasAngles = b
                                  }) s = 
  (if b then "<" else "") ++ scheme
  ++ iriAuthToString iuserinfomap authority ""
  ++ show path ++ query ++ fragment ++ (if b then ">" else "") ++ s


iriToStringAbbrev :: IRI -> ShowS
iriToStringAbbrev (IRI { prefixName = pname
                       , iriPath = aPath
                       , iriQuery = aQuery
                       , iriFragment = aFragment
                       }) =
  (pname ++) . (show aPath ++) . (aQuery ++) . (aFragment ++)

iriToStringAbbrevMerge :: IRI -> ShowS
iriToStringAbbrevMerge (IRI { iriPath = aPath
                            , iriQuery = aQuery
                            , iriFragment = aFragment
                            }) =
  (show aPath ++) . (aQuery ++) . (aFragment ++)

iriAuthToString :: (String -> String) -> Maybe IRIAuth -> ShowS
iriAuthToString _ Nothing = id          -- shows ""
iriAuthToString iuserinfomap
        (Just IRIAuth { iriUserInfo = uinfo
                      , iriRegName = regname
                      , iriPort = iport
                      } ) =
    ("//" ++) . (if null uinfo then id else (iuserinfomap uinfo ++))
             . (regname ++)
             . (iport ++)

-- * Resolving a relative IRI relative to a base IRI

isDefined :: String -> Bool
isDefined = not . null

{- | Returns a new 'IRI' which represents the value of the
first 'IRI' interpreted as relative to the second 'IRI'.
For example:

> "foo" `relativeTo` "http://bar.org/" = "http://bar.org/foo"

-}
relativeTo :: IRI -> IRI -> Maybe IRI
relativeTo ref base
    | isDefined ( iriScheme ref ) =
        just_isegments ref
    | isJust ( iriAuthority ref ) =
        just_isegments ref { iriScheme = iriScheme base }
    | isDefined $ getFstString $ iriPath ref = 
            just_isegments ref
                { iriScheme = iriScheme base
                , iriAuthority = iriAuthority base
                , iriPath = if head (getFstString $ iriPath ref) == '/' 
                            then iriPath ref
                            else stringToId $ mergePaths base ref
                }
    | isDefined ( iriQuery ref ) =
        just_isegments ref
            { iriScheme = iriScheme base
            , iriAuthority = iriAuthority base
            , iriPath = iriPath base
            }
    | otherwise =
        just_isegments ref
            { iriScheme = iriScheme base
            , iriAuthority = iriAuthority base
            , iriPath = iriPath base
            , iriQuery = iriQuery base
            }
    where
        getFstString anId = case getTokens anId of 
           (Token s _):_ -> s
           _ -> error $ "can't get first string from an empty id"        
        just_isegments u =
            Just $ u { iriPath = removeDotSegments (iriPath u) }
        mergePaths b r
            | isJust (iriAuthority b) && null pbs = '/' : prs
            | otherwise = dropLast pbs ++ prs
            where
                pb = iriPath b
                pr = iriPath r
                pbs = getFstString pb
                prs = getFstString pr
        dropLast = fst . splitLast -- reverse . dropWhile (/='/') . reverse

-- Remove dot isegments, but protect leading '/' character
removeDotSegments :: Id -> Id
removeDotSegments i = case getTokens i of
  [] -> error $ "Cannot remove dots from empty id:" ++ show i
  (Token s r):_ -> let 
    t' = Token (removeDotSegmentsString s) r
   in simpleIdToId t' 

removeDotSegmentsString :: String -> String
removeDotSegmentsString ('/' : ps) = '/' : elimDots ps []
removeDotSegmentsString ps = elimDots ps []

-- Second arg accumulates isegments processed so far in reverse order
elimDots :: String -> [String] -> String
elimDots "" rs = concat (reverse rs)
elimDots "." rs = elimDots "" rs
elimDots ( '.' : '/' : ps) rs = elimDots ps rs
elimDots ".." rs = elimDots [] (drop 1 rs)
elimDots ( '.' : '.' : '/' : ps) rs = elimDots ps (drop 1 rs)
elimDots ps rs = elimDots ps1 (r : rs)
    where
        (r, ps1) = nextSegment ps

{- Returns the next isegment and the rest of the path from a path string.
Each isegment ends with the next '/' or the end of string. -}
nextSegment :: String -> (String, String)
nextSegment ps =
    case break (== '/') ps of
        (r, '/' : ps1) -> (r ++ "/", ps1)
        (r, _) -> (r, [])

-- Split last (name) isegment from path, returning (path,name)
splitLast :: String -> (String, String)
splitLast path = (reverse revpath, reverse revname)
    where
        (revname, revpath) = break (== '/') $ reverse path

-- * Finding a IRI relative to a base IRI

{- | Returns a new 'IRI' which represents the relative location of
the first 'IRI' with respect to the second 'IRI'.  Thus, the
values supplied are expected to be absolute IRIs, and the result
returned may be a relative IRI.

Example:

> "http://example.com/Root/sub1/name2#frag"
>   `relativeFrom` "http://example.com/Root/sub2/name2#frag"
>   == "../sub1/name2#frag"

There is no single correct implementation of this function,
but any acceptable implementation must satisfy the following:

> (uabs `relativeFrom` ubase) `relativeTo` ubase == uabs

For any valid absolute IRI.
(cf. <http://lists.w3.org/Archives/Public/iri/2003Jan/0008.html>
<http://lists.w3.org/Archives/Public/iri/2003Jan/0005.html>) -}
relativeFrom :: IRI -> IRI -> IRI
relativeFrom uabs base
    | diff iriScheme uabs base = uabs
    | diff iriAuthority uabs base = uabs { iriScheme = "" }
    | diff iriPath uabs base = uabs
        { iriScheme = ""
        , iriAuthority = Nothing
        , iriPath = let
                      i1 = iriPath uabs
                      i2 = iriPath base
                    in case (getTokens i1, getTokens i2) of
                        ((Token s1 _):_ , (Token s2 _):_) ->  
                             stringToId $ relPathFrom 
                                  (removeBodyDotSegments s1)
                                  (removeBodyDotSegments s2)
                        _ -> error $ "empty id:" ++ show i1 ++ " " ++ show i2
        }
    | diff iriQuery uabs base = uabs
        { iriScheme = ""
        , iriAuthority = Nothing
        , iriPath = mkId []
        }
    | otherwise = uabs          -- Always carry fragment from uabs
        { iriScheme = ""
        , iriAuthority = Nothing
        , iriPath = mkId []
        , iriQuery = ""
        }
    where
        diff :: Eq b => (a -> b) -> a -> a -> Bool
        diff sel u1 u2 = sel u1 /= sel u2
        -- Remove dot isegments except the final isegment
        removeBodyDotSegments p = removeDotSegmentsString p1 ++ p2
            where
               (p1, p2) = splitLast p

relPathFrom :: String -> String -> String
relPathFrom [] _ = "/"
relPathFrom pabs [] = pabs
relPathFrom pabs base =                 -- Construct a relative path isegments
    if sa1 == sb1                       -- if the paths share a leading isegment
        then if sa1 == "/"              -- other than a leading '/'
            then if sa2 == sb2
                then relPathFrom1 ra2 rb2
                else pabs
            else relPathFrom1 ra1 rb1
        else pabs
    where
        (sa1, ra1) = nextSegment pabs
        (sb1, rb1) = nextSegment base
        (sa2, ra2) = nextSegment ra1
        (sb2, rb2) = nextSegment rb1

{- relPathFrom1 strips off trailing names from the supplied paths,
and calls difPathFrom to find the relative path from base to
target -}
relPathFrom1 :: String -> String -> String
relPathFrom1 pabs base = relName
    where
        (sa, na) = splitLast pabs
        (sb, nb) = splitLast base
        rp = relSegsFrom sa sb
        relName = if null rp then
                      if na == nb then ""
                      else if protect na then "./" ++ na
                      else na
                  else
                      rp ++ na
        -- Precede name with some path if it is null or contains a ':'
        protect n = null n || ':' `elem` n

{- relSegsFrom discards any common leading isegments from both paths,
then invokes difSegsFrom to calculate a relative path from the end
of the base path to the end of the target path.
The final name is handled separately, so this deals only with
"directory" segtments. -}
relSegsFrom :: String -> String -> String
relSegsFrom [] [] = ""      -- paths are identical
relSegsFrom sabs base =
    if sa1 == sb1
        then relSegsFrom ra1 rb1
        else difSegsFrom sabs base
    where
        (sa1, ra1) = nextSegment sabs
        (sb1, rb1) = nextSegment base

{- difSegsFrom calculates a path difference from base to target,
not including the final name at the end of the path
(i.e. results always ends with '/')

This function operates under the invariant that the supplied
value of sabs is the desired path relative to the beginning of
base.  Thus, when base is empty, the desired path has been found. -}
difSegsFrom :: String -> String -> String
difSegsFrom sabs "" = sabs
difSegsFrom sabs base = difSegsFrom ("../" ++ sabs) (snd $ nextSegment base)

-- * Other normalization functions

{- |Expands a CURIE to an IRI. @Nothing@ iff there is no IRI @i@ assigned
to the prefix of @c@ or the concatenation of @i@ and @iriPath c@
is not a valid IRI. -}
expandCurie :: Map String IRI -> IRI -> Maybe IRI
expandCurie prefixMap c =  
  if hasFullIRI c then Just c else
  case Map.lookup (filter (/= ':') $ prefixName c) prefixMap of
    Nothing -> Nothing
    Just i -> case mergeCurie c i of
      Nothing -> Nothing
      Just j -> Just $ if null $ iriScheme i then j { iriPos = iriPos c }
        else j
        { prefixName = prefixName c
        , iriPath = iriPath c
        , iriQuery = iriQuery c
        , iriFragment = iriFragment c
        , iriPos = iriPos c }

setAngles :: Bool -> IRI -> IRI
setAngles b i = i { hasAngles = b }

{- |'mergeCurie' merges the CURIE @c@ into IRI @i@, appending their string
representations -}
mergeCurie :: IRI -> IRI -> Maybe IRI
mergeCurie c i =
  let s = iriToStringFull id (setAngles False i) ""
        ++ iriToStringAbbrevMerge c ""
  in parseIRICurie $ if null $ iriScheme i then s else '<' : s ++ ">"

deleteQuery :: IRI -> IRI
deleteQuery i = i { iriQuery = "" }

addSuffixToIRI :: String -> IRI -> IRI
addSuffixToIRI s i = if not $ null $ iriQuery i 
                   then i{iriQuery = iriQuery i ++ s}
                  else  
                        i{iriPath  = appendId (iriPath i) (stringToId s)}

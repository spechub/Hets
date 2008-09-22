{- |
Module      :  $Header$
Description :  HXT-related functions for reading and writing XML
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (depends on HXT)

functions for handling xml
-}

module OMDoc.XmlHandling
  (
     applyXmlFilter
    ,withValue
    ,withQualValue
    ,withSValue
    ,withQualSValue
    ,getQualValue
    ,XmlName
    ,XmlNameList
    ,XmlNamed(..)
    ,xmlNL
    ,xmlNullFilter
    ,getChild
    ,adjustStringForXmlName
    ,createUniqueName
    ,createXmlNames
    ,createXmlNamesCon
    ,uniqueXmlNames
    ,uniqueXmlNamesContainer
    ,uniqueXmlNamesContainerExt
    ,attributeCon
    ,attributeWithXmlNamesCon
    ,qualattr
    ,createAttributed
    ,createQAttributed
    ,xpipe
  )
  where

import OMDoc.Util
import OMDoc.Container

-- Often used symbols from HXT
import Text.XML.HXT.Parser ( (.>), (+=), getValue, hasAttr )

import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)

import Text.XML.HXT.RelaxNG.Validator
import Text.XML.HXT.Arrow.ReadDocument
import Text.XML.HXT.Arrow.XmlIOStateArrow

import Data.List (find)
import Data.Char (isDigit, isAlpha, isAlphaNum, isAscii, isControl, ord)

xpipe::forall c a b . (a->[b]) -> (b->[c]) -> a -> [c]
xpipe = (.>)

-- | applys a filter to XmlTrees (returns resulting tree)
applyXmlFilter::HXT.XmlFilter->HXT.XmlTrees->HXT.XmlTrees
applyXmlFilter f t = (id .> f) t

-- | newline in XML
xmlNL::(HXT.XmlTree->HXT.XmlTrees)
xmlNL = HXT.txt "\n"

xmlNullFilter::HXT.XmlFilter
xmlNullFilter = \_ -> []

-- XMLFilter 'hasValue' only gives back the value, not the tree...
-- | filters nodes with a special value
withValue::String->(String -> Bool)->HXT.XmlFilter
withValue s f t = if (HXT.hasValue s f t) /= [] then [t] else []

getChild::Int->HXT.XmlFilter
getChild c (HXT.NTree _ cs) = singleitem c cs

-- | filters nodes with a special value in a certain namespace
-- will also use a matching value without namespace
withQualValue::String->String->(String->Bool)->HXT.XmlFilter
withQualValue "" local test t = withValue local test t
withQualValue prefix local test t =
  if withValue (prefix++":"++local) test t /= []
    then
      [t]
    else
      if withValue local test t /= []
        then
          [t]
        else
          []

-- | shortcut for checking a value against an exact reference value
withSValue::String->String->HXT.XmlFilter
withSValue a v = withValue a (==v)

-- | 'withSValue' for namespaces
withQualSValue::String->String->String->HXT.XmlFilter
withQualSValue prefix local v = withQualValue prefix local (==v)

-- | retrieves a qualified value (prefix:localpart) from xml
-- but tries also without prefix, if no such value can be found...
getQualValue::String->String->HXT.XmlFilter
getQualValue "" localpart = getValue localpart
getQualValue prefix localpart =
  (\t -> if hasAttr (prefix ++ ":" ++ localpart) t /= []
    then
      getValue (prefix ++ ":" ++ localpart) t
    else
      getValue localpart t
  )

type XmlName = String
-- this type is used to store already used names
type XmlNameList = [XmlName]

data XmlNamed a = XmlNamed { xnItem::a, xnName::XmlName }

instance (Eq a)=>Eq (XmlNamed a) where
  x1 == x2 = (xnItem x1) == (xnItem x2)

instance (Ord a)=>Ord (XmlNamed a) where
  compare x1 x2 = compare (xnItem x1) (xnItem x2)

instance (Show a)=>Show (XmlNamed a) where
  show x = (show $ xnItem x) ++ " xml:(" ++ (xnName x) ++ ")"

-- | remove characters from a String to use it in xml
-- follows the xml Name-production-rule (without combining-char and extender)
adjustStringForXmlName::String->XmlName
adjustStringForXmlName [] = "Empty"
adjustStringForXmlName s@(firstChar:_) =
  preventEmpty $
    if (isDigit firstChar)
      then
        adjustStringForXmlName ("N"++s)
      else
        filter
          (\c ->
            -- xml-names may contain letters, digits and
            -- the symbols shown below
            (isAscii c) && ((isAlphaNum c) || (elem c ['_','.','-'])) -- removed ':'
          )
          -- remove everything until a letter or ':' or '_' is found
          (dropWhile
            (\c ->
              not ((isAlpha c) || (elem c [':', '_']))
            )
            (replaceSpecial s)
          )
  where
    replaceSpecial::String->String
    replaceSpecial [] = []
--  replaceSpecial ('\194':r) = replaceSpecial r -- an A circumflex
    replaceSpecial (c:r) =
      case c of
        ' ' -> "_"
        '*' -> "Ast"
        '<' -> "Lower"
        '>' -> "Greater"
        ':' -> "Colon"
        ';' -> "SemiColon"
        '/' -> "Division"
        '+' -> "Plus"
        '-' -> "Minus"
        '%' -> "Percent"
        '(' -> "BrackOpen"
        ')' -> "BrackClose"
        '{' -> "BraceOpen"
        '}' -> "BraceClose"
        '[' -> "SBrackOpen"
        ']' -> "SBrackClose"
        '=' -> "Equals"
        ',' -> "Comma"
        '#' -> "Hash"
--        '\'' -> "SQuote"
        '\'' -> "-prime" -- more apropriate ?
        '"' -> "Quote"
        '~' -> "Tilde"
        '`' -> "AccGrav"
        '\\' -> "Backslash"
        '!' -> "Excla"
        '?' -> "Quest"
        '@' -> "At"
        '$' -> "Dollar"
        '&' -> "Amp"
        '^' -> "Power"
        '\167' -> "Para"
        '\176' -> "Degree"
        _ ->
          if isAscii c && (not $ isControl c)
            then
              [c]
            else
              ("c" ++ (show $ ord c))
      ++ replaceSpecial r
    preventEmpty::String->String
    preventEmpty [] = "Empty"
    preventEmpty q = q

-- creates a unique name from an initial name and a list of used names
-- the returned string will be the initial name or the initial name with a
-- number appended
createUniqueName::XmlNameList->String->String
createUniqueName
  xmlnames initialname =
    initialname ++
      (nzshow
        (until
          (\n -> not $ elem (initialname ++ (nzshow n)) xmlnames)
          (+1)
          0
        )
      )
  where
  nzshow::Int->String
  nzshow 0 = ""
  nzshow i = show i

-- | create unique xml-names for a list of items with a list of previous names
-- and a naming function and return resulting list and list of used names
createXmlNames::(a->String)->XmlNameList->[a]->([XmlNamed a], XmlNameList)
createXmlNames = createXmlNamesCon

-- | create unique names for items in a container with a list of previous names
-- and a naming function and return a container of named elements and a list
-- of used names
createXmlNamesCon::(Container q a, Container r (XmlNamed a))=>(a->String)->XmlNameList->q->(r, XmlNameList)
createXmlNamesCon nameForItem xmlnames container =
  let
    items = getItems container
    (newitems, newnames) = foldl (\(items' , xmlnames' ) item ->
        let
          initialname = adjustStringForXmlName (nameForItem item)
          finalitemname = createUniqueName xmlnames' initialname
        in
          (items' ++ [XmlNamed item finalitemname], finalitemname:xmlnames' )
      ) ([], xmlnames) items
  in
    (fromItems newitems, newnames)

-- | create unique names for a list of items providing a function to check if
-- two elements are equal
uniqueXmlNames::XmlNameList->(a->a->Bool)->(a->String)->[a]->([XmlNamed a], XmlNameList)
uniqueXmlNames xmlnames isequal tostring =
  foldl (\(xmlnamed, xmlnames' ) listitem ->
    let
      initialname = adjustStringForXmlName (tostring listitem)
      itemname = createUniqueName xmlnames' initialname
    in
      case find ((isequal listitem) . xnItem) xmlnamed of
        Nothing ->
          ( (XmlNamed listitem itemname):xmlnamed, itemname:xmlnames' )
        (Just previous) ->
          ((XmlNamed listitem (xnName previous)):xmlnamed , xmlnames' )
  ) ([],xmlnames)

-- | unique xml names for container
uniqueXmlNamesContainer::(Container c i, Container d (XmlNamed i))=>
  XmlNameList
  -> (a->String) -- ^ how to find an initial name for a converted item
  -> c
  -> (i->i->Bool)
  -> (i->a) -- ^ specify a conversion of items (or 'id')
  -> (d, XmlNameList)
uniqueXmlNamesContainer
  xmlnames
  tostring
  container
  isequal
  conversion =
    let
      items = getItems container
      (newitems, newxmlnames) =
        foldl(\(newitems' , newxmlnames' ) listitem ->
            let
              converted = conversion listitem
              initialname = adjustStringForXmlName (tostring converted)
              itemname = createUniqueName newxmlnames' initialname
            in
              case find ((isequal listitem) . xnItem) newitems' of
                Nothing ->
                  ( (XmlNamed listitem itemname):newitems' , itemname:newxmlnames' )
                (Just previous) ->
                  ((XmlNamed listitem (xnName previous)):newitems' , newxmlnames' )
        ) ([], xmlnames) items
    in
      (fromItems newitems, newxmlnames)

-- | unique xml names for container
uniqueXmlNamesContainerExt::(Container c i, Container d j)=>
  XmlNameList
  -> (a->String) -- ^ how to find an initial name for a converted item
  -> c
  -> (a->a->Bool)
  -> (i->a) -- ^ specify a conversion of items (or 'id')
  -> (i->XmlName->j)
  -> (d, XmlNameList)
uniqueXmlNamesContainerExt
  xmlnames
  tostring
  container
  isequal
  extract
  synthesize =
    let
      items = getItems container
      (newitems, newxmlnames) =
        foldl(\(newitems' , newxmlnames' ) listitem ->
            let
              extracted = extract listitem
              initialname = adjustStringForXmlName (tostring extracted)
              itemname = createUniqueName newxmlnames' initialname
            in
              case find ((isequal extracted) . extract . fst) newitems' of
                Nothing ->
                  ( (listitem, itemname):newitems' , itemname:newxmlnames' )
                (Just (_, pname)) ->
                  ( (listitem, pname):newitems' , newxmlnames' )
          ) ([], xmlnames) items
    in
      (fromItems (map (uncurry synthesize) newitems), newxmlnames)

attributeCon::(Container c a, Container d b, Container q r)=>
  (a->b->Bool)->
  a->
  (a->b->r)->
  c->
  d->
  q
attributeCon
  attribmatch
  defaultAttribute
  attribute
  source
  target =
  let
    attributeitems = getItems source
    targetitems = getItems target
    newitems = map (\i ->
      attribute
        (case find ((flip attribmatch) i) attributeitems of
          Nothing -> defaultAttribute
          (Just attribItem) -> attribItem)
        i) targetitems
  in
    fromItems newitems

attributeWithXmlNamesCon::(Container c (XmlNamed a), Container d b, Container q r)=>
  (a->b->Bool)->
  (XmlName->b->r)
  ->c
  ->d
  ->q
attributeWithXmlNamesCon
  matched
  attribute =
  attributeCon
    (\a b -> matched (xnItem a) b)
    (error "Unknown Element!")
    (\a b -> attribute (xnName a) b)

-- shortcut to create an attribute with a qualified name (but no namespace uri)
-- leave prefix (p) blank to just have a normal attribute
qualattr::String->String->String->HXT.XmlFilter
qualattr p a v = HXT.qattr (HXT.mkPrefixLocalPart p a) (HXT.mkXText v)
--qualattr p a v = HXT.qattr (HXT.mkPrefixLocalPart "" a) (HXT.mkXText v)

-- creates a tag with qualified attributes (p,a,v) (no namespace uri)
createQAttributed::String->[(String,String,String)]->HXT.XmlFilter
createQAttributed tagname attributes =
  foldl (\tag' (p, a, v) -> tag' += qualattr p a v) (HXT.etag tagname) attributes

-- creates a tag with unqualified attributes (a,v)
createAttributed::String->[(String,String)]->HXT.XmlFilter
createAttributed tagname attributes =
  createQAttributed tagname $ map (\(a, v) -> ("", a, v) ) attributes

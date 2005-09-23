-- |
-- Xml Parsec parser with pure filter interface
--
-- Version : $Id$


module Text.XML.HXT.Parser.XmlParsec
    ( sPace
    , sPace0
    , skipS
    , skipS0
    , asciiLetter
    , keyword
    , name
    , ncName
    , qName
    , names
    , nmtoken
    , nmtokens
    , entityValue
    , attrValue
    , attrChar'
    , systemLiteral
    , pubidLiteral
    , charData
    , charData'
    , comment
    , pI
    , cDSect
    , document
    , document'
    , prolog
    , xMLDecl
    , xMLDecl'
    , versionInfo
    , misc
    , doctypedecl
    , markupdecl
    , sDDecl
    , element
    , content
    , contentWithTextDecl
    , reference
    , reference'
    , charRef
    , entityRef
    , textDecl
    , encodingDecl
    , dq
    , sq
    , eq
    , gt
    , lt
    , separator
    , allBut
    , xread

    , parseXmlAttrListBody
    , parseXmlAttrValue
    , parseXmlContent
    , parseXmlContentSpec
    , parseXmlDocEncodingSpec
    , parseXmlDocument
    , parseXmlDTDPart
    , parseXmlDTDTokens
    , parseXmlEncodingSpec
    , parseXmlEntityEncodingSpec
    , parseXmlEntityValue
    , parseXmlGeneralEntityValue
    , parseXmlPart
    , parseXmlText

    , parseNMToken
    , parseName
    , substXmlEntities
    , xmlEntities
    )
where

import Text.XML.HXT.DOM.XmlTree hiding (choice)
import qualified Text.XML.HXT.DOM.XmlTree as XmlTree

import Text.ParserCombinators.Parsec
    ( Parser
    , parse
    -- , parseTest
    , (<?>), (<|>)
    , char
    , digit
    , hexDigit
    , satisfy
    , string
    , eof 
    , between
    , choice
    , many, many1
    , noneOf
    , oneOf, option
    , sepBy1
    , skipMany, skipMany1
    , try
    , notFollowedBy
    , unexpected
    , getPosition
    , sourceName
    )

import Text.XML.HXT.Parser.XmlCharParser
    ( xmlChar
    , xmlNameChar
    , xmlNameStartChar
    , xmlNCNameChar
    , xmlNCNameStartChar
    , xmlSpaceChar
    )

import Text.XML.HXT.DOM.Unicode
    ( isXmlChar
    , intToCharRef
    , intToCharRefHex
    )

import Text.XML.HXT.DOM.Util
    ( hexStringToInt
    , decimalStringToInt
    )

import Data.Char
    ( toLower
    )

import Data.Maybe

-- ------------------------------------------------------------
--
-- Character (2.2) and White Space (2.3)
--
-- Unicode parsers in module XmlCharParser

-- ------------------------------------------------------------

sPace		:: Parser String
sPace
    = many1 xmlSpaceChar

sPace0		:: Parser String
sPace0
    = many xmlSpaceChar

skipS		:: Parser ()
skipS
    = skipMany1 xmlSpaceChar

skipS0		:: Parser ()
skipS0
    = skipMany xmlSpaceChar

-- ------------------------------------------------------------
--
-- Names and Tokens (2.3)

asciiLetter		:: Parser Char
asciiLetter
    = satisfy (\ c -> ( c >= 'A' && c <= 'Z' ||
			c >= 'a' && c <= 'z' )
	      )
      <?> "ASCII letter"

name		:: Parser String
name
    = try ( do
	    s1 <- xmlNameStartChar
	    sl <- many xmlNameChar
	    return (s1 : sl)
	  )
      <?> "Name"

-- Namespaces in XML: Rules [4-5] NCName:

ncName		:: Parser String
ncName
    = try ( do
	    s1 <- xmlNCNameStartChar
	    sl <- many xmlNCNameChar
	    return (s1 : sl)
	  )
      <?> "NCName"

-- Namespaces in XML: Rules [6-8] QName:

qName		:: Parser (String, String)
qName
    = do
      s1 <- ncName
      s2 <- option "" ( do
			char ':'
			ncName
		      )
      return ( if null s2 then (s2, s1) else (s1, s2) )

names		:: Parser [String]
names
    = sepBy1 name sPace

nmtoken		:: Parser String
nmtoken
    = try (many1 xmlNameChar)
      <?> "Nmtoken"

nmtokens	:: Parser [String]
nmtokens
    = sepBy1 nmtoken sPace

name'		:: Parser XmlTree
name'
    = do
      n <- name
      return (mkXDTDTree NAME [(a_name, n)] [])

nmtoken'	:: Parser XmlTree
nmtoken'
    = do
      n <- nmtoken
      return (mkXDTDTree NAME [(a_name, n)] [])

-- ------------------------------------------------------------
--
-- Literals (2.3)

singleChar		:: String -> Parser Char
singleChar notAllowed
    = satisfy (\ c -> isXmlChar c && not (c `elem` notAllowed))

entityValue	:: Parser XmlTrees
entityValue
    =  do
       sl <- between dq dq (many $ entityChar "%&\"")
       return sl
       <|>
       do
       sl <- between sq sq (many $ entityChar "%&\'")
       return sl
       <?> "entity value (in quotes)"

entityChar	:: String -> Parser XmlTree
entityChar notAllowed
    = peReference'
      <|>
      reference'
      <|>
      ( do
	cs <- many1 (singleChar notAllowed)
	return (mkXTextTree cs)
      )

--

attrValue	:: Parser XmlTrees
attrValue
    = between dq dq (attrValue' "<&\"")
      <|>
      between sq sq (attrValue' "<&\'")
      <?> "attribute value (in quotes)"

attrValue'	:: String -> Parser XmlTrees
attrValue' notAllowed
    = many ( reference' <|> attrChar' notAllowed)

attrChar'	:: String -> Parser XmlTree
attrChar' notAllowed
    = do
      cs <- many1 (singleChar notAllowed)
      return (mkXTextTree cs)

--

attrValueDQ	:: Parser String
attrValueDQ
    = between dq dq (concRes $ many $ attrChar "<&\"")

attrValueSQ	:: Parser String
attrValueSQ
    = between sq sq (concRes $ many $ attrChar "<&\'")

attrValueQ	:: Parser String
attrValueQ
    = ( do
	v <- attrValueDQ
	return ("\"" ++ v ++ "\"")
      )
      <|>
      ( do
	v <- attrValueSQ
	return ("'" ++ v ++ "'")
      )
      <?> "attribute value (in quotes)"

attrChar	:: String -> Parser String
attrChar notAllowed
    = reference
      <|>
      mkList (singleChar notAllowed)
      <?> "legal attribute character or reference"

--

systemLiteral		:: Parser String
systemLiteral
    = between dq dq (many $ noneOf "\"")
      <|>
      between sq sq (many $ noneOf "\'")
      <?> "system literal (in quotes)"

pubidLiteral		:: Parser String
pubidLiteral
    = between dq dq (many $ pubidChar "\'")
      <|>
      between sq sq (many $ pubidChar "")
      <?> "pubid literal (in quotes)"
      where
      pubidChar		:: String -> Parser Char
      pubidChar quoteChars
	  = asciiLetter
	    <|>
	    digit
	    <|>
	    oneOf " \r\n"		-- no "\t" allowed, so xmlSpaceChar parser not used
	    <|>
	    oneOf "-()+,./:=?;!*#@$_%"
            <|>
	    oneOf quoteChars

entityValue'	:: Parser (Attributes, XmlTrees)
entityValue'
    = do
      v <- entityValue
      return ([], v)

-- ------------------------------------------------------------
--
-- Character Data (2.4)

charData		:: Parser XmlTrees
charData
    = many (charData' <|> reference')

charData'		:: Parser XmlTree
charData'
    = try ( do
	    t <- allBut1 many1 (\ c -> not (c `elem` "<&")) "]]>"
	    return (mkXTextTree t)
	  )

-- ------------------------------------------------------------
--
-- Comments (2.5)

comment		:: Parser XmlTree

comment
    = ( do
	c <- between (try $ string "<!--") (string "-->") (allBut many "--")
	return (mkXCmtTree c)
      ) <?> "comment"

-- ------------------------------------------------------------
--
-- Processing Instructions

pI		:: Parser XmlTree
pI
    = between (try $ string "<?") (string "?>")
      ( do
	n <- pITarget
	p <- option "" (do
			sPace
			allBut many "?>"
		       )
	return (mkXPiTree n p)
      ) <?> "processing instruction"
      where
      pITarget	:: Parser String
      pITarget = ( do
		   n <- name
		   if map toLower n == t_xml
		      then unexpected n
		      else return n
		 )

-- ------------------------------------------------------------
--
-- CDATA Sections (2.7)

cDSect		:: Parser XmlTree

cDSect
    = do
      t <- between ( try $ string "<![CDATA[") (string "]]>") (allBut many "]]>")
      return (mkXCdataTree t)
      <?> "CDATA section"

-- ------------------------------------------------------------
--
-- Document (2.1) and Prolog (2.8)

document	:: Parser XmlTree
document
    = do
      pos <- getPosition
      dl <- document'
      return ( (head . replaceChildren dl)
	       $ newDocument (sourceName pos)
	     )

document'	:: Parser XmlTrees
document'
    = do
      pl <- prolog
      el <- element
      ml <- many misc
      eof
      return (pl ++ [el] ++ ml)

prolog		:: Parser XmlTrees
prolog
    = do
      xml     <- option [] xMLDecl'
      misc1   <- many misc
      dtdPart <- option [] doctypedecl
      misc2   <- many misc
      return (xml ++ misc1 ++ dtdPart ++ misc2)

xMLDecl		:: Parser XmlTrees
xMLDecl
    = between (try $ string "<?xml") (string "?>")
      ( do
	vi <- versionInfo
	ed <- option [] encodingDecl
	sd <- option [] sDDecl
	skipS0
	return (vi ++ ed ++ sd)
      )
      <?> "xml declaration"

xMLDecl'	:: Parser XmlTrees
xMLDecl'
    = do
      al <- xMLDecl
      return [mkXmlDeclTree al]

xMLDecl''	:: Parser XmlTree
xMLDecl''
    = do
      al     <- option [] (try xMLDecl)
      return (newRoot al)

versionInfo	:: Parser XmlTrees
versionInfo
    = ( do
	try ( do
	      skipS
	      keyword a_version
	    )
	eq
	vi <- quoted versionNum
	return (xattr a_version vi)
      )
      <?> "version info (with quoted version number)"

versionNum	:: Parser String
versionNum
    = many1 xmlNameChar

eq		:: Parser ()
eq
    = try ( do
	    skipS0
	    char '='
	    skipS0
	    return ()
	  )
      <?> "="

misc		:: Parser XmlTree
misc
    = comment
      <|>
      pI
      <|>
      ( ( do
	  ws <- sPace
	  return (mkXTextTree ws)
	) <?> ""
      )

-- ------------------------------------------------------------
--
-- Document Type definition (2.8)

doctypedecl	:: Parser XmlTrees
doctypedecl
    = between (try $ string "<!DOCTYPE") (char '>')
      ( do
	skipS
	n <- name
	exId <- option [] ( try ( do
				  skipS
				  externalID
				)
			  )
	skipS0
	markup <- option []
	          ( do
		    m <- between (char '[' ) (char ']') markupOrDeclSep
		    skipS0
		    return m
		  )
	return [mkXDTDTree DOCTYPE ((a_name, n) : exId) markup]
      )

markupOrDeclSep	:: Parser XmlTrees
markupOrDeclSep
    = ( do
	ll <- many ( markupdecl
		     <|>
		     declSep
		     <|>
		     mkList conditionalSect
		   )
	return (concat ll)
      )

declSep		:: Parser XmlTrees
declSep
    = mkList peReference'
      <|>
      ( do
	skipS
	return []
      )

markupdecl	:: Parser XmlTrees
markupdecl
    = mkList
      ( attrlistDecl
        <|>
        elementdecl
	<|>
	entityDecl
	<|>
	notationDecl
	<|>
	pI
	<|>
	comment
      )

-- ------------------------------------------------------------
--
--

-- ------------------------------------------------------------
--
-- Standalone Document Declaration (2.9)

sDDecl		:: Parser XmlTrees
sDDecl
    = do
      try (do
	   skipS
	   keyword a_standalone
	  )
      eq
      sd <- quoted yesNo
      return (xattr a_standalone sd)
      where
      yesNo = ( ( do
		  keyword v_yes
		  return v_yes
		)
		<|>
		( do
		  keyword v_no
		  return v_no
		)
	      )

-- ------------------------------------------------------------
--
-- element, tags and content (3, 3.1)

element		:: Parser XmlTree
element
    = ( do
	e <- elementStart
	elementRest e
      ) <?> "element"

elementStart		:: Parser (String, [(String, XmlTrees)])
elementStart
    = do
      n <- ( try ( do
		   char '<'
		   n <- name
		   return n
		 )
	     <?> "start tag"
	   )
      ass <- attrList
      skipS0
      return (n, ass)
      where
      attrList
	  = option [] ( do
			skipS
			attrList'
		      )
      attrList'
	  = option [] ( do
			a1 <- attribute
			al <- attrList
			let (n, _v) = a1
			if isJust . lookup n $ al
			  then unexpected ("attribute name " ++ show n ++ " occurs twice in attribute list")
			  else return (a1 : al)
		      )

elementRest	:: (String, [(String, XmlTrees)]) -> Parser XmlTree
elementRest (n, al)
    = ( do
	try $ string "/>"
	return (mkXTagTree n (map (uncurry mkXAttrTree) al) [])
      )
      <|>
      ( do
	gt
	c <- content
	eTag n
	return (mkXTagTree n (map (uncurry mkXAttrTree) al) c)
      )
      <?> "proper attribute list followed by \"/>\" or \">\""

eTag		:: String -> Parser ()
eTag n'
    = do
      try ( string "</" ) <?> ""
      n <- name
      skipS0
      gt
      if n == n'
	 then return ()
	 else unexpected ("illegal end tag </" ++ n ++ "> found, </" ++ n' ++ "> expected")

attribute	:: Parser (String, XmlTrees)
attribute
    = do
      n <- name
      eq
      v <- attrValue
      return (n, v)

content		:: Parser XmlTrees
content
    = do
      c1 <- charData
      cl <- many
	    ( do
	      l <- ( element
		     <|>
		     cDSect
		     <|>
		     pI
		     <|>
		     comment
		   )
	      c <- charData
	      return (l : c)
	    )
      return (c1 ++ concat cl)

contentWithTextDecl	:: Parser XmlTrees
contentWithTextDecl
    = do
      option [] textDecl
      content

-- ------------------------------------------------------------
--
-- Element Type Declarations (3.2)

elementdecl	:: Parser XmlTree
elementdecl
    = between (try $ string "<!ELEMENT") (char '>')
      ( do
	skipS
	n <- name
	skipS
	(al, cl) <- contentspec
	skipS0
	return (mkXDTDTree ELEMENT ((a_name, n) : al) cl)
      )

contentspec	:: Parser (Attributes, XmlTrees)
contentspec
    = simplespec k_empty v_empty
      <|>
      simplespec k_any v_any
      <|>
      mixed
      <|>
      children
      <|>
      peReference'''
      <?> "content specification"
    where
    simplespec kw v
	= do
	  keyword kw
	  return ([(a_type, v)], [])

contentspec'	:: Parser XmlTrees
contentspec'
    = do
      (al, cl) <- contentspec
      return [mkXDTDTree ELEMENT al cl]

-- ------------------------------------------------------------
--
-- Element Content (3.2.1)

children	:: Parser (Attributes, XmlTrees)
children
    = ( do
	(al, cl) <- choiceOrSeq
	modifier <- optOrRep
	return ([(a_type, v_children)], [mkXDTDTree CONTENT (modifier ++ al) cl])
      )
      <?> "element content"

optOrRep	:: Parser Attributes
optOrRep
    = do
      m <- option "" (mkList (oneOf "?*+"))
      return [(a_modifier, m)]

choiceOrSeq	:: Parser (Attributes, XmlTrees)
choiceOrSeq
    = do
      cl <- try ( do
		  lpar
		  choiceOrSeqBody
		)
      rpar
      return cl

choiceOrSeqBody	:: Parser (Attributes, XmlTrees)
choiceOrSeqBody
    = do
      cp' <- cp
      choiceOrSeq1 cp'
    where
    choiceOrSeq1:: XmlTree -> Parser (Attributes, XmlTrees)
    choiceOrSeq1 c1
	= ( do
	    bar
	    c2 <- cp
	    cl <- many ( do
			 bar
			 cp
		       )
	    return ([(a_kind, v_choice)], (c1 : c2 : cl))
	  )
	  <|>
	  ( do
	    cl <- many ( do
			 comma
			 cp
		       )
	    return ([(a_kind, v_seq)], (c1 : cl))
	  )
          <?> "sequence or choice"

{-
choiceOrSeqBody'	:: Parser XmlTrees
choiceOrSeqBody'
    = do
      (al, cl) <- choiceOrSeqBody
      return [ mkXDTDTree CONTENT al cl ]
-}

cp		:: Parser XmlTree
cp
    = ( do
	n <- ( name'
	       <|>
	       peReference'
	     )
	m <- optOrRep
	return ( case m of
		 [(_, "")] -> n
		 _         -> mkXDTDTree CONTENT (m ++ [(a_kind, v_seq)]) [n]
	       )
      )
      <|>
      ( do
	(al, cl) <- choiceOrSeq
	m <- optOrRep
	return (mkXDTDTree CONTENT (m ++ al) cl)
      )


-- ------------------------------------------------------------
--
-- Mixed Content (3.2.2)

mixed		:: Parser (Attributes, XmlTrees)
mixed
    = ( do
	try ( do
	      lpar
	      string k_pcdata
	    )
	nl <- many ( do
		     bar
		     ( name'
		       <|>
		       peReference' )
		   )
	rpar
	if null nl
          then do
	       option ' ' (char '*')		-- (#PCDATA) or (#PCDATA)* , both are legal
	       return ( [ (a_type, v_pcdata) ]
		      , []
		      )
	  else do
	       char '*' <?> "closing parent for mixed content (\")*\")"
	       return ( [ (a_type, v_mixed) ]
		      , [ mkXDTDTree CONTENT [ (a_modifier, "*")
					     , (a_kind, v_choice)
					     ] nl
			]
		      )
      )
      <?> "mixed content"

{-
mixedBody	:: Parser (Attributes, XmlTrees)
mixedBody
    = do
      try (string k_pcdata)
      nl <- many ( do
		   bar
		   name'
		 )
      return ( if null nl
	       then ( [(a_type, v_pcdata)]
		    , []
		    )
	       else ( [(a_type, v_mixed)]
		    , [ mkXDTDTree CONTENT [ (a_modifier, "*")
					   , (a_kind, v_choice)
					   ] nl
		      ]
		    )
	     )
-}

-- ------------------------------------------------------------
--
-- Attribute-List Declarations (3.3)
-- attribute lists are parsed i two steps,
-- first a list of "tokens" is parsed inclusive parameter entity references (attrlistDecl)
-- in a second step after PE substitution the text is parsed again (attrlistBody)
-- with the syntax rules from the XML spec (without PE refs)

attrlistDecl		:: Parser XmlTree
attrlistDecl
    = between (try $ string "<!ATTLIST") ( char '>' <?> "attribute type or default declaration" )
      ( do
	el <- dtdTokens
	return (mkXDTDTree ATTLIST [] el)
      )

dtdTokens		:: Parser XmlTrees
dtdTokens
    = do
      ts <- many dtdToken
      return (concat ts)
      where
      ws = mkXTextTree " "
      dtdToken
	  = ( do
	      t <- peReference'
	      return [ws, t, ws]
	    )
	    <|>
	    ( do
	      ts <- between lpar rpar dtdTokens
	      return ([mkXTextTree "("] ++ ts ++ [mkXTextTree ")"])
	    )
	    <|>
	    mkList
	    ( ( do
		skipS
		return ws
	      )
	      <|>
	      nmtoken'
	      <|>
	      ( do
		v <- attrValueQ
		return (mkXTextTree v)
	      )
	      <|>
	      ( do
		c <- oneOf "#|"
		return (mkXTextTree [c])
	      )
	    )

attrlistBody		:: Parser XmlTrees
attrlistBody
    = do
      skipS
      n <- name
      attrDefList n

attrDefList		:: String -> Parser XmlTrees
attrDefList attrName
    = do
      al <- many attrDef
      skipS0
      return (map (mkDTree attrName) al)
      where
      mkDTree n' (al, cl)
	  = mkXDTDTree ATTLIST ((a_name, n') : al) cl

attrDef		:: Parser (Attributes, XmlTrees)
attrDef
    = do
      n <- try ( do
		 skipS0
		 name
	       ) <?> "attribute name"
      skipS
      (t, cl) <- attrType
      skipS
      d <- defaultDecl
      return (((a_value, n) : d) ++ t, cl)

attrType	:: Parser (Attributes, XmlTrees)
attrType
    = tokenizedOrStringType
      <|>
      enumeration
      <|>
      notationType
      <?> "attribute type"

{-
attrType'	:: Parser XmlTrees
attrType'
    = do
      (al, cl) <- attrType
      return [mkXDTDTree ATTLIST al cl]
-}

tokenizedOrStringType	:: Parser (Attributes, XmlTrees)
tokenizedOrStringType
    = do
      n <- choice $ map keyword typl
      return ([(a_type, n)], [])
      where
      typl	= [ k_cdata
		  , k_idrefs
		  , k_idref
		  , k_id
		  , k_enitity
		  , k_entities
		  , k_nmtokens
		  , k_nmtoken
		  ]

enumeration	:: Parser (Attributes, XmlTrees)
enumeration
    = do
      nl <- between lpar rpar ( sepBy1 nmtoken' bar )
      return ([(a_type, k_enumeration)], nl)

notationType	:: Parser (Attributes, XmlTrees)
notationType
    = do
      keyword k_notation
      skipS
      nl <- between lpar rpar ( sepBy1 name' bar )
      return ([(a_type, k_notation)], nl)

defaultDecl	:: Parser Attributes
defaultDecl
    = ( do
	str <- try $ string k_required
	return [(a_kind, str)]
      )
      <|>
      ( do
	str <- try $ string k_implied
	return [(a_kind, str)]
      )
      <|>
      ( do
        l <- fixed
	v <- attrValue
	return ((a_default, xshow v) : l)
      )
      <?> "default declaration"
    where
    fixed = option [(a_kind, k_default)]
	    ( do
	      try $ string k_fixed
	      skipS
	      return [(a_kind, k_fixed)]
	    )

-- ------------------------------------------------------------
--
-- Conditional Sections (3.4)
--
-- conditional sections are parsed in two steps,
-- first the whole content is detected,
-- and then, after PE substitution include sections are parsed again

conditionalSect		:: Parser XmlTree
conditionalSect
    = do
      try $ string "<!["
      skipS0
      c1 <- ( ( do
		keyword k_include
		return (mkXTextTree k_include)
	      )
	      <|>
	      ( do
		keyword k_ignore
		return (mkXTextTree k_ignore)
	      )
	      <|>
	      peReference'
	    )
      skipS0
      char '['
      cs <- condSectCont
      return (mkXDTDTree CONDSECT [] (c1 : [mkXTextTree cs]))
    where

    condSectCont	:: Parser String
    condSectCont
	= ( do
	    try $ string "]]>"
	    return ""
	  )
          <|>
	  ( do
	    try $ string "<!["
	    cs1 <- condSectCont
	    cs2 <- condSectCont
	    return ("<![" ++ cs1 ++ "]]>" ++ cs2)
	  )
	  <|>
	  ( do
	    c  <- xmlChar
	    cs <- condSectCont
	    return (c : cs)
	  )

-- ------------------------------------------------------------
--
-- Character and Entity References (4.1)

reference	:: Parser String
reference
    = ( do
	i <- charRef
	return ("&#" ++ show i ++ ";")
      )
      <|>
      ( do
        n <- entityRef
        return ("&" ++ n ++ ";")
      )
      

checkCharRef	:: Int -> Parser Int
checkCharRef i
    = if ( i <= fromEnum (maxBound::Char)
	   && isXmlChar (toEnum i)
	 )
        then return i
	else unexpected ("illegal value in character reference: " ++ intToCharRef i ++ " , in hex: " ++ intToCharRefHex i)

charRef		:: Parser Int
charRef
    = do
      try (string "&#x")
      d <- many1 hexDigit
      semi
      checkCharRef (hexStringToInt d)
      <|>
      do
      try (string "&#")
      d <- many1 digit
      semi
      checkCharRef (decimalStringToInt d)
      <?> "character reference"


entityRef	:: Parser String
entityRef
    = do
      char '&'
      n <- name
      semi
      return n
      <?> "entity reference"

peReference	:: Parser String
peReference
    = try ( do
	    char '%'
	    n <- name
	    semi
	    return n
	  )
      <?> "parameter-entity reference"

reference'	:: Parser XmlTree
reference'
    = charRef'
      <|>
      entityRef'

charRef'	:: Parser XmlTree
charRef'
    = do
      i <- charRef
      return (mkXCharRefTree i)

entityRef'	:: Parser XmlTree
entityRef'
    = do
      n <- entityRef
      return (mkXEntityRefTree n)

peReference'	:: Parser XmlTree
peReference'
    = do
      r <- peReference
      return (mkXPERefTree r)

peReference'''	:: Parser (Attributes, XmlTrees)
peReference'''
    = do
      r <- peReference'
      return ( [ (a_type,  k_peref) ]
	     , [r]
	     )

-- ------------------------------------------------------------
--
-- Entity Declarations (4.2)

entityDecl		:: Parser XmlTree
entityDecl
    = between ( try $ string "<!ENTITY" ) (char '>')
      ( do
	skipS
	( peDecl
	  <|>
	  geDecl
	  <?> "entity declaration" )
      )

geDecl			:: Parser XmlTree
geDecl
    = do
      n <- name
      skipS
      (al, cl) <- entityDef
      skipS0
      return ( mkXDTDTree ENTITY ((a_name, n) : al) cl )

entityDef		:: Parser (Attributes, XmlTrees)
entityDef
    = entityValue'
      <|>
      externalEntitySpec

externalEntitySpec	:: Parser (Attributes, XmlTrees)
externalEntitySpec
    = do
      al <- externalID
      nd <- option [] nDataDecl
      return ((al ++ nd), [])

peDecl			:: Parser XmlTree
peDecl
    = do
      char '%'
      skipS
      n <- name
      skipS
      (al, cs) <- peDef
      skipS0
      return ( mkXDTDTree PENTITY ((a_name, n) : al) cs )

peDef			:: Parser (Attributes, XmlTrees)
peDef
    = entityValue'
      <|>
      do
      al <- externalID
      return (al, [])

-- ------------------------------------------------------------
--
-- External Entities (4.2.2)

externalID	:: Parser Attributes
externalID
    = ( do
	keyword k_system
	skipS
	lit <- systemLiteral
	return [(k_system, lit)]
      )
      <|>
      ( do
	keyword k_public
	skipS
	pl <- pubidLiteral
	skipS
	sl <- systemLiteral
	return [ (k_system, sl)
	       , (k_public, pl) ]
      )
      <?> "SYSTEM or PUBLIC declaration"

nDataDecl	:: Parser Attributes
nDataDecl
    = do
      try ( do
	    skipS
	    keyword k_ndata
	  )
      skipS
      n <- name
      return [(k_ndata, n)]

-- ------------------------------------------------------------
--
-- Text Declaration (4.3.1)

textDecl	:: Parser XmlTrees
textDecl
    = between (try $ string "<?xml") (string "?>")
      ( do
	vi <- option [] versionInfo
	ed <- encodingDecl
	skipS0
	return (vi ++ ed)
      )
      <?> "text declaration"


textDecl''	:: Parser XmlTree
textDecl''
    = do
      al    <- option [] (try textDecl)
      return (newRoot al)

-- ------------------------------------------------------------
--
-- external parsed entity (4.3.2)

-- ------------------------------------------------------------
--
-- Encoding Declaration (4.3.3)

encodingDecl	:: Parser XmlTrees
encodingDecl
    = do
      try (do
	   skipS
	   keyword a_encoding
	  )
      eq
      ed <- quoted encName
      return (xattr a_encoding ed)

encName		:: Parser String
encName
    = do
      c <- asciiLetter
      r <- many (asciiLetter <|> digit <|> oneOf "._-")
      return (c:r)

-- ------------------------------------------------------------
--
-- Notation Declarations (4.7)

notationDecl		:: Parser XmlTree
notationDecl
    = between (try $ string "<!NOTATION") (char '>' <?> "notation declaration")
      ( do
	skipS
	n <- name
	skipS
	eid <- ( try externalID
		 <|>
		 publicID
	       )
	skipS0
	return (mkXDTDTree NOTATION ((a_name, n) : eid) [])
      )

publicID		:: Parser Attributes
publicID
    = do
      keyword k_public
      skipS
      l <- pubidLiteral
      return [(k_public, l)]

-- ------------------------------------------------------------
--
-- simple char parsers

dq,
 sq, lt, gt, semi	:: Parser Char

dq	= char '\"'
sq	= char '\''
lt	= char '<'
gt	= char '>'
semi	= char ';'

separator	:: Char -> Parser ()
separator c
    = do
      try ( do
	    skipS0
	    char c
	  )
      skipS0
      <?> [c]

bar,
 comma, lpar, rpar	:: Parser ()

bar	= separator '|'
comma	= separator ','

lpar
    = do
      char '('
      skipS0

rpar
    = do
      skipS0
      char ')'
      return ()

-- ------------------------------------------------------------
--
-- own combinators

-- ------------------------------------------------------------
--

{-
tok		:: Parser a -> Parser ()
tok p
    = do
      _ <- p
      return ()
-}

-- ------------------------------------------------------------
--
-- keywords

keyword		:: String -> Parser String
keyword kw
    = try ( do
	    n <- name
	    if n == kw
	      then return n
	      else unexpected n
	  )
      <?> kw

-- ------------------------------------------------------------
--
-- concatenate parse results

concRes		:: Parser [String] -> Parser String
concRes p
    = do
      sl <- p
      return (concat sl)


mkList		:: Parser a -> Parser [a]
mkList p
    = do
      r <- p
      return [r]

{-
concList	:: (Parser [a] -> Parser [[a]]) -> Parser [a] -> Parser [a]
concList loop p
    =  do
       sl <- loop p
       return (concat sl)
-}

-- ------------------------------------------------------------
--
-- all chars but not a special substring

allBut		:: (Parser Char -> Parser String) -> String -> Parser String
allBut p str
    = allBut1 p (const True) str

allBut1		:: (Parser Char -> Parser String) -> (Char -> Bool) -> String -> Parser String
allBut1 p prd (c:rest)
    = p ( satisfy (\ x -> isXmlChar x && prd x && not (x == c) )
	  <|>
	  try ( do
		char c
		notFollowedBy ( do
				try (string rest)
				return c
			      )
		return c
	      )
	)

allBut1 _p _prd str
    = error ("allBut1 _ _ " ++ show str ++ " is undefined")

-- ------------------------------------------------------------
--
-- parser for quoted attribute values

quoted		:: Parser a -> Parser a
quoted p
    = between dq dq p
      <|>
      between sq sq p

-- ------------------------------------------------------------

parseOptTextDecl	:: Bool -> Parser a -> Parser a
parseOptTextDecl True p
    = do
      option [] textDecl
      p

parseOptTextDecl False p
    = p

-- ------------------------------------------------------------
--
-- the main entry points:
--	parsing the content of a text node
--	or parsing the text children from a tag node

-- |
-- the inverse function to 'xshow', (for XML content).
--
-- the string parameter is parsed with the XML content parser.
-- result is the list of trees or in case of an error a single element list with the
-- error message as node. No entity or character subtitution is done.
-- For substitution of predefined XML entities 'substXmlEntities' can be used.
--
-- see also: 'parseXmlContent', 'substXmlEntities'

xread			:: String -> XmlTrees
xread str
    = parseXmlFromString parser loc str
    where
    loc = "string: " ++ show (if length str > 40 then take 40 str ++ "..." else str)
    parser = do
	     res <- content		-- take the content parser for parsing the string
	     eof			-- and test on everything consumed
	     return res

-- |
-- the filter version of 'xread'

parseXmlContent		:: XmlFilter
parseXmlContent
    = xread . xshow . this

-- |
-- a more general version of 'parseXmlContent'.
-- The parser to be used and the context are extra parameter

parseXmlText		:: Parser XmlTrees -> String -> XmlFilter
parseXmlText p loc	= parseXmlFromString p loc . xshow . this

parseXmlDocument	:: String -> String -> XmlTrees
parseXmlDocument	= parseXmlFromString document'


parseXmlFromString	:: Parser XmlTrees -> String -> String -> XmlTrees
parseXmlFromString parser loc
    = either (xerr . (++ "\n") . show) id . parse parser loc

-- ------------------------------------------------------------

-- |
-- general parser for parsing arbitray parts of a XML document

parseXmlPart	:: Parser XmlTrees -> String -> Bool -> String -> XmlFilter
parseXmlPart parser expected ext context t
    = parseXmlText ( do
		     res <- (parseOptTextDecl ext parser)
		     eof <?> expected
		     return res
		   ) context
      $ t

-- ------------------------------------------------------------

-- |
-- Parser for parts of a DTD

parseXmlDTDPart	:: Bool -> String -> XmlFilter
parseXmlDTDPart
    = parseXmlPart markupOrDeclSep "markup declaration"

-- ------------------------------------------------------------

-- |
-- Parser for general entites

parseXmlGeneralEntityValue	:: Bool -> String -> XmlFilter
parseXmlGeneralEntityValue
    = parseXmlPart content "general entity value"

-- ------------------------------------------------------------

-- |
-- Parser for attribute values

parseXmlAttrValue	:: String -> XmlFilter
parseXmlAttrValue
    = parseXmlPart (attrValue' "<&") "attribute value" False

-- ------------------------------------------------------------

-- |
-- Parser for entity values

parseXmlEntityValue	:: Bool -> String -> XmlFilter
parseXmlEntityValue
    = parseXmlPart ( many $ entityChar "%&" ) "entity value"

-- ------------------------------------------------------------

-- |
-- Parser for ATTLIST declarations

parseXmlAttrListBody	:: Bool -> String -> XmlFilter
parseXmlAttrListBody
    = parseXmlPart attrlistBody "ATTLIST declaration after parameter substitution"

-- ------------------------------------------------------------

-- |
-- Parser for substituted parameter entity references

parseXmlDTDTokens	:: Bool -> String -> XmlFilter
parseXmlDTDTokens
    = parseXmlPart dtdTokens "parameter entity reference in DTD part"

-- ------------------------------------------------------------

-- |
-- Parser for content specification within a DTD

parseXmlContentSpec	:: String -> XmlFilter
parseXmlContentSpec
    = parseXmlPart (contentspec') "content specification" False

-- ------------------------------------------------------------

-- |
-- Parser for NMTOKENs

parseNMToken		:: String -> XmlFilter
parseNMToken
    = parseXmlPart (many1 nmtoken') "nmtoken" False

-- ------------------------------------------------------------

-- |
-- Parser for XML names

parseName		:: String -> XmlFilter
parseName
    = parseXmlPart (many1 name') "name" False

-- ------------------------------------------------------------

-- |
-- try to parse a xml encoding spec.
--
--
--    * 1.parameter encParse :  the parser for the encoding decl
--
--    - 2.parameter root :  a document root
--
--    - returns : the same tree, but with an additional
--			  attribute "encoding" in the root node
--			  in case of a valid encoding spec
--			  else the unchanged tree

parseXmlEncodingSpec	:: Parser XmlTree -> XmlFilter
parseXmlEncodingSpec encDecl
    =  parseEncSpec
      `when` isRoot
      where
      parseEncSpec r
	  = case ( parse encDecl source . xshow . getChildren $ r ) of
	    Right t
		-> addAttrl (const (getAttrl t)) r
	    Left _
		-> this r
	  where
	  source = valueOf a_source r

parseXmlEntityEncodingSpec	:: XmlFilter
parseXmlEntityEncodingSpec	= parseXmlEncodingSpec textDecl''

parseXmlDocEncodingSpec		:: XmlFilter
parseXmlDocEncodingSpec		= parseXmlEncodingSpec xMLDecl''

-- ------------------------------------------------------------

-- |
-- Filter for substitution of all occurences the predefined XML entites quot, amp, lt, gt, apos
-- by equivalent character references

substXmlEntities	:: XmlFilter
substXmlEntities
    = XmlTree.choice
      [ isXEntityRef	:-> substEntity
      , isXTag		:-> processAttr (processChildren substXmlEntities)
      , this		:-> this
      ]
      where
      substEntity t'@(NTree (XEntityRef en) _)
	  = case (lookup en xmlEntities) of
	    Just i
		-> [mkXCharRefTree i]
	    Nothing
		-> this t'

      substEntity _					-- just for preventing ghc warning
	  = error "substXmlEntities: illegal argument"

-- |
-- list of predefined XML entity names and their unicode values
--
-- used by 'substXmlEntities'

xmlEntities	:: [(String, Int)]
xmlEntities	= [ ("quot",	34)
		  , ("amp",	38)
		  , ("lt",	60)
		  , ("gt",	62)
		  , ("apos",	39)
		  ]

-- ------------------------------------------------------------

-- |
-- HTML Parser
--
-- Version : $Id$
--
-- This parser tries to interprete everything as HTML
-- no errors are emitted during parsing. If something looks
-- weired, warning messages are inserted in the document tree

module Text.XML.HXT.Parser.HtmlParser
    ( getHtmlDoc
    , parseHtmlDoc
    , runHtmlParser
    , substHtmlEntities
    )

where

import Text.XML.HXT.DOM.XmlTree
import Text.XML.HXT.DOM.XmlState

import Text.ParserCombinators.Parsec
    ( Parser
    , SourcePos
    , anyChar
    , between
    , char
    , eof
    , getPosition
    , many
    , noneOf
    , option
    , string
    , try
    , (<|>)
    )
import Text.XML.HXT.Parser.XmlParser
    ( allBut
    , attrChar'
    , cDSect
    , charData'
    , doctypedecl
    , dq
    , eq
    , gt
    , misc
    , name
    , parseXmlText
    , pI
    , reference'
    , skipS0
    , sq
    , xMLDecl'
    )

import Text.XML.HXT.Parser.XmlCharParser
    ( xmlChar
    )

import Text.XML.HXT.Parser.XmlInput
    ( getXmlContents
    )

import Text.XML.HXT.Parser.XmlOutput
    ( traceTree
    , traceSource
    , traceMsg
    )

import Data.Maybe
    ( fromMaybe
    )
import Data.Char
    ( toLower
    )

-- ------------------------------------------------------------

-- |
-- read a document and parse it with 'parseHtmlDoc'. The main entry point of this module
--
-- The input tree must be a root tree like in 'getXmlDoc'. The content is read with 'getXmlContents',
-- is parsed with 'parseHtmlDoc' and canonicalized (char refs are substituted in content and attributes,
-- but comment is preserved)
--
-- see also : 'getWellformedDoc'

getHtmlDoc	:: XmlStateFilter state
getHtmlDoc
    = setSystemParams
      .>>
      getXmlContents
      .>>
      parseHtmlDoc

-- | The HTML parsing filter
--
-- The input is parsed with 'runHtmlParser', everything is interpreted as HTML,
-- if errors ocuur, the parser will try to do some meaningfull action and continues
-- parsing. Afterwards the entitiy references for defined for XHTML are resovled,
-- any unresolved reference is transformed into plain text.
--
-- Error messages
-- during parsing and entity resolving are added as warning nodes into the resulting tree.
--
-- The warnings are issued, if the 1. parameter noWarnings is set to True,
-- afterwards all are removed from the resulting tree.

parseHtmlDoc	:: XmlStateFilter a
parseHtmlDoc
    = parseDoc
      `whenM` ( isRoot .> getChildren .> isXText )
      where
      parseDoc t'
	  = ( traceMsg 2 ("parseHtmlDoc: parse HTML document " ++ show loc)
	      .>>
	      runHtmlParser
	      .>>
	      liftMf (processTopDown substHtmlEntities)
	      .>>
	      removeWarnings
	      .>>
	      traceTree
	      .>>
	      traceSource
              ) $ t'
	  where
	  loc    = valueOf a_source t'			-- get document source uri

      removeWarnings	:: XmlStateFilter a
      removeWarnings t'
	  = let
	    noWarnings  = not (satisfies (hasOption a_issue_warnings) t')
	    selWarnings = deep
			  ( choice [ isWarning :-> this
				   , isXTag    :-> (getAttrl .> selWarnings)
				   ]
			  )
	    remWarnings = processTopDown
			  ( choice [ isWarning :-> none
				   , isXTag    :-> (processAttrl (remWarnings $$))
				   , this      :-> this
				   ]
			  )
	    warnings = selWarnings t'
	    in do 
	       if null warnings
		  then thisM t'
		  else do
		       if noWarnings
			  then return []
			  else do
			       issueError $$< warnings
		       return (remWarnings t')

-- | The pure HTML parser, usually called via 'parseHtmlDoc'.
--

runHtmlParser	:: XmlStateFilter a
runHtmlParser t
    = if null errs
      then do
	   return (replaceChildren res t)
      else do
	   issueError $$< errs
	   return (setStatus c_err "parsing HTML" t)
      where
      res  = getChildren .> parseXmlText htmlDocument loc $ t
      errs = isXError .> neg isWarning $$ res
      loc  = valueOf a_source t


-- ------------------------------------------------------------

htmlDocument	:: Parser XmlTrees
htmlDocument
    = do
      pl <- htmlProlog
      el <- htmlContent
      eof
      return (pl ++ el)

htmlProlog	:: Parser XmlTrees
htmlProlog
    = do
      xml <- option []
	     ( try xMLDecl'
	       <|>
	       ( do
		 pos <- getPosition
		 try (string "<?")
		 return $ xwarn (show pos ++ " wrong XML declaration")
	       )
	     )
      misc1   <- many misc
      dtdPart <- option []
		 ( try doctypedecl
		   <|>
		   ( do
		     pos <- getPosition
		     try (string "<!DOCTYPE")
		     return $ xwarn (show pos ++ " HTML DOCTYPE declaration ignored")
		   )
		 )
      return (xml ++ misc1 ++ dtdPart)

htmlContent	:: Parser XmlTrees
htmlContent
    = option []
      ( do
	context <- hContent ([], [])
	pos     <- getPosition
	return $ closeTags pos context
      )
      where
      closeTags _ (body, [])
	  = reverse body
      closeTags pos' (body, ((tn, al, body1) : restOpen))
	  = closeTags pos' (addHtmlWarn (show pos' ++ ": no closing tag found for \"<" ++ tn ++ " ...>\"")
			    .
			    addHtmlTag tn al body
			    $
			    (body1, restOpen)
			   )

type OpenTags	= [(String, XmlTrees, XmlTrees)]
type Context	= (XmlTrees, OpenTags)

hElement	:: Context -> Parser Context
hElement context
    = ( do
	t <- hSimpleData
	return (addHtmlElems [t] context)
      )
      <|>
      hOpenTag context
      <|>
      hCloseTag context
      <|>
      ( do			-- wrong tag, take it as text
	pos <- getPosition
	c   <- xmlChar
	return ( addHtmlWarn (show pos ++ " char " ++ show c ++ " not allowed in this context")
		 .
		 addHtmlElems (xtext [c])
		 $
		 context
	       )
      )
      <|>
      ( do
	pos <- getPosition
	c <- anyChar
	return ( addHtmlWarn ( show pos
			       ++ " illegal data in input or illegal XML char "
			       ++ show c
			       ++ " found and ignored, possibly wrong encoding scheme used")
		 $
		 context
	       )
      )


hSimpleData	:: Parser XmlTree
hSimpleData
    = charData'
      <|>
      try reference'
      <|>
      try hComment
      <|>
      pI
      <|>
      cDSect

hCloseTag	:: Context -> Parser Context
hCloseTag context
    = do
      n <- try ( do
		 string "</"
		 lowerCaseName
	       )
      skipS0
      pos <- getPosition
      checkSymbol gt ("closing > in tag \"</" ++ n ++ "\" expected") (closeTag pos n context)

hOpenTag	:: Context -> Parser Context
hOpenTag context
    = ( do
	pos <- getPosition
	e   <- hOpenTagStart
	hOpenTagRest pos e context
      )

hOpenTagStart	:: Parser (String, XmlTrees)
hOpenTagStart
    = do
      n <- try ( do
		 char '<'
		 n <- lowerCaseName
		 return n
	       )
      skipS0
      as <- hAttrList
      return (n, as)

hOpenTagRest	:: SourcePos -> (String, XmlTrees) -> Context -> Parser Context
hOpenTagRest pos (tn, al) context
    = ( do
	try $ string "/>"
	return (addHtmlTag tn al [] context)
      )
      <|>
      ( do
	context1 <- checkSymbol gt ("closing > in tag \"<" ++ tn ++ "...\" expected") context
	if isEmptyTag tn
	   then return (addHtmlTag tn al [] context1)
	   else return (openTag tn al . closePrevTag pos tn $ context1)
      )

hAttrList	:: Parser XmlTrees
hAttrList
    = many (try hAttribute)
      where
      hAttribute
	  = do
	    n <- name
	    v <- hAttrValue
	    skipS0
	    return $ mkXAttrTree n v

hAttrValue	:: Parser XmlTrees
hAttrValue
    = option []
      ( try ( do
	      eq
	      hAttrValue'
	    )
      )

hAttrValue'	:: Parser XmlTrees
hAttrValue'
    = try ( between dq dq (hAttrValue'' "&\"") )
      <|>
      try ( between sq sq (hAttrValue'' "&\'") )
      <|>
      ( do			-- HTML allows unquoted attribute values
	cs <- many (noneOf " \r\t\n>\"\'")
	return [mkXTextTree cs]
      )

hAttrValue''	:: String -> Parser XmlTrees
hAttrValue'' notAllowed
    = many ( hReference' <|> attrChar' notAllowed)

hReference'	:: Parser XmlTree
hReference'
    = try reference'
      <|>
      ( do
	char '&'
	return (mkXTextTree "&")
      )

hContent	:: Context -> Parser Context
hContent context
    = option context
      ( do
	context1 <- hElement context
	hContent context1
      )

-- hComment allows "--" in comments
-- comment from XML spec does not

hComment		:: Parser XmlTree
hComment
    = do
      c <- between (try $ string "<!--") (string "-->") (allBut many "-->")
      return (mkXCmtTree c)

checkSymbol	:: Parser a -> String -> Context -> Parser Context
checkSymbol p msg context
    = do
      pos <- getPosition
      option (addHtmlWarn (show pos ++ " " ++ msg) context)
       ( do 
	 try p
	 return context
       )

lowerCaseName	:: Parser String
lowerCaseName
    = do
      n <- name
      return (map toLower n)

-- ------------------------------------------------------------

addHtmlTag	:: String -> XmlTrees -> XmlTrees -> Context -> Context
addHtmlTag tn al body (body1, openTags)
    = (xtag tn al (reverse body) ++ body1, openTags)

addHtmlWarn	:: String -> Context -> Context
addHtmlWarn msg
    = addHtmlElems (xwarn msg)

addHtmlElems	:: XmlTrees -> Context -> Context
addHtmlElems elems (body, openTags)
    = (reverse elems ++ body, openTags)

openTag		:: String -> XmlTrees -> Context -> Context
openTag tn al (body, openTags)
    = ([], (tn, al, body) : openTags)

closeTag	:: SourcePos -> String -> Context -> Context
closeTag pos n context
    | n `elem` (map ( \ (n1, _, _) -> n1) $ snd context)
	= closeTag' n context
    | otherwise
	= addHtmlWarn (show pos ++ " no opening tag found for </" ++ n ++ ">")
	  .
	  addHtmlTag n [] []
          $
	  context
    where
    closeTag' n' (body', (n1, al1, body1) : restOpen)
	= close context1
	  where
	  context1
	      = addHtmlTag n1 al1 body' (body1, restOpen)
	  close
	      | n' == n1
		= id
	      | n1 `isInnerTagOf` n'
		  = closeTag pos n'
	      | otherwise
		= addHtmlWarn (show pos ++ " no closing tag found for \"<" ++ n1 ++ " ...>\"")
		  .
		  closeTag' n'
    closeTag' _ _
	= error "illegal argument for closeTag'"

closePrevTag	:: SourcePos -> String -> Context -> Context
closePrevTag _pos _n context@(_body, [])
    = context
closePrevTag pos n context@(body, (n1, al1, body1) : restOpen)
    | n `closes` n1
	= closePrevTag pos n
	  ( addHtmlWarn (show pos ++ " tag \"<" ++ n1 ++ " ...>\" implicitly closed by opening tag \"<" ++ n ++ " ...>\"")
	    .
	    addHtmlTag n1 al1 body
	    $
	    (body1, restOpen)
	  )
    | otherwise
	= context

-- ------------------------------------------------------------
--
-- taken from HaXml and extended

isEmptyTag	:: String -> Bool
isEmptyTag n	= n `elem`
		  [ "area"
		  , "base"
		  , "br"
		  , "col"
		  , "frame"
		  , "hr"
		  , "img"
		  , "input"
		  , "link"
		  , "meta"
		  , "param"
		  ]

isInnerTagOf	:: String -> String -> Bool
n `isInnerTagOf` tn
    = n `elem`
      ( fromMaybe [] . lookup tn
      $ [ ("body",    ["p"])
	, ("caption", ["p"])
	, ("dd",      ["p"])
	, ("div",     ["p"])
	, ("dl",      ["dt","dd"])
	, ("dt",      ["p"])
	, ("li",      ["p"])
	, ("map",     ["p"])
	, ("object",  ["p"])
	, ("ol",      ["li"])
	, ("table",   ["th","tr","td","thead","tfoot","tbody"])
	, ("tbody",   ["th","tr","td"])
	, ("td",      ["p"])
	, ("tfoot",   ["th","tr","td"])
	, ("th",      ["p"])
	, ("thead",   ["th","tr","td"])
	, ("tr",      ["th","td"])
	, ("ul",      ["li"])
	]
      )

closes :: String -> String -> Bool
"a"	`closes` "a"					= True
"li"	`closes` "li"					= True
"th"	`closes`  t    | t `elem` ["th","td"]		= True
"td"	`closes`  t    | t `elem` ["th","td"]		= True
"tr"	`closes`  t    | t `elem` ["th","td","tr"]	= True
"dt"	`closes`  t    | t `elem` ["dt","dd"]		= True
"dd"	`closes`  t    | t `elem` ["dt","dd"]		= True
"colgroup" 
	`closes` "colgroup"				= True
"form"	`closes` "form"					= True
"label"	`closes` "label"				= True
"map"	`closes` "map"					= True
"object"
	`closes` "object"				= True
_	`closes` t  | t `elem` ["option"
			       ,"script"
			       ,"style"
			       ,"textarea"
			       ,"title"
			       ]			= True
t	`closes` "select" | t /= "option"		= True
"thead"	`closes` t  | t `elem` ["colgroup"]		= True
"tfoot"	`closes` t  | t `elem` ["thead"
			       ,"colgroup"]		= True
"tbody"	`closes` t  | t `elem` ["tbody"
			       ,"tfoot"
			       ,"thead"
			       ,"colgroup"]		= True
t	`closes` t2 | t `elem` ["h1","h2","h3"
			       ,"h4","h5","h6"
			       ,"dl","ol","ul"
			       ,"table"
			       ,"div","p"
			       ]
		      &&
                      t2 `elem` ["h1","h2","h3"
				,"h4","h5","h6"
				,"p","div"
				]			= True
_	`closes` _					= False

-- ------------------------------------------------------------
--
-- XHTML entities

substHtmlEntities	:: XmlFilter
substHtmlEntities
    = choice [ isXEntityRef	:-> substEntity
	     , isXTag		:-> processAttr (processChildren substHtmlEntities)
	     , this		:-> this
	     ]
      where
      substEntity t'@(NTree (XEntityRef en) _)
	  = case (lookup en xhtmlEntities) of
	    Just i
		-> [mkXCharRefTree i]
	    Nothing
		-> xwarn ("no XHTML entity found for reference: \"&" ++ en ++ ";\"")
		   ++
		   (xmlTreesToText [t'])

      substEntity _
	  = error "substHtmlEntities: illegal argument"

xhtmlEntities	:: [(String, Int)]
xhtmlEntities	= [ ("quot",	34)
		  , ("amp",	38)
		  , ("lt",	60)
		  , ("gt",	62)
		  , ("apos",	39)

		  , ("nbsp",	160)
		  , ("iexcl",	161)
		  , ("cent",	162)
		  , ("pound",	163)
		  , ("curren",	164)
		  , ("yen",	165)
		  , ("brvbar",	166)
		  , ("sect",	167)
		  , ("uml",	168)
		  , ("copy",	169)
		  , ("ordf",	170)
		  , ("laquo",	171)
		  , ("not",	172)
		  , ("shy",	173)
		  , ("reg",	174)
		  , ("macr",	175)
		  , ("deg",	176)
		  , ("plusmn",	177)
		  , ("sup2",	178)
		  , ("sup3",	179)
		  , ("acute",	180)
		  , ("micro",	181)
		  , ("para",	182)
		  , ("middot",	183)
		  , ("cedil",	184)
		  , ("sup1",	185)
		  , ("ordm",	186)
		  , ("raquo",	187)
		  , ("frac14",	188)
		  , ("frac12",	189)
		  , ("frac34",	190)
		  , ("iquest",	191)
		  , ("Agrave",	192)
		  , ("Aacute",	193)
		  , ("Acirc",	194)
		  , ("Atilde",	195)
		  , ("Auml",	196)
		  , ("Aring",	197)
		  , ("AElig",	198)
		  , ("Ccedil",	199)
		  , ("Egrave",	200)
		  , ("Eacute",	201)
		  , ("Ecirc",	202)
		  , ("Euml",	203)
		  , ("Igrave",	204)
		  , ("Iacute",	205)
		  , ("Icirc",	206)
		  , ("Iuml",	207)
		  , ("ETH",	208)
		  , ("Ntilde",	209)
		  , ("Ograve",	210)
		  , ("Oacute",	211)
		  , ("Ocirc",	212)
		  , ("Otilde",	213)
		  , ("Ouml",	214)
		  , ("times",	215)
		  , ("Oslash",	216)
		  , ("Ugrave",	217)
		  , ("Uacute",	218)
		  , ("Ucirc",	219)
		  , ("Uuml",	220)
		  , ("Yacute",	221)
		  , ("THORN",	222)
		  , ("szlig",	223)
		  , ("agrave",	224)
		  , ("aacute",	225)
		  , ("acirc",	226)
		  , ("atilde",	227)
		  , ("auml",	228)
		  , ("aring",	229)
		  , ("aelig",	230)
		  , ("ccedil",	231)
		  , ("egrave",	232)
		  , ("eacute",	233)
		  , ("ecirc",	234)
		  , ("euml",	235)
		  , ("igrave",	236)
		  , ("iacute",	237)
		  , ("icirc",	238)
		  , ("iuml",	239)
		  , ("eth",	240)
		  , ("ntilde",	241)
		  , ("ograve",	242)
		  , ("oacute",	243)
		  , ("ocirc",	244)
		  , ("otilde",	245)
		  , ("ouml",	246)
		  , ("divide",	247)
		  , ("oslash",	248)
		  , ("ugrave",	249)
		  , ("uacute",	250)
		  , ("ucirc",	251)
		  , ("uuml",	252)
		  , ("yacute",	253)
		  , ("thorn",	254)
		  , ("yuml",	255)

		  , ("OElig",	338)
		  , ("oelig",	339)
		  , ("Scaron",	352)
		  , ("scaron",	353)
		  , ("Yuml",	376)
		  , ("circ",	710)
		  , ("tilde",	732)

		  , ("ensp",	8194)
		  , ("emsp",	8195)
		  , ("thinsp",	8201)
		  , ("zwnj",	8204)
		  , ("zwj",	8205)
		  , ("lrm",	8206)
		  , ("rlm",	8207)
		  , ("ndash",	8211)
		  , ("mdash",	8212)
		  , ("lsquo",	8216)
		  , ("rsquo",	8217)
		  , ("sbquo",	8218)
		  , ("ldquo",	8220)
		  , ("rdquo",	8221)
		  , ("bdquo",	8222)
		  , ("dagger",	8224)
		  , ("Dagger",	8225)
		  , ("permil",	8240)
		  , ("lsaquo",	8249)
		  , ("rsaquo",	8250)
		  , ("euro",	8364)

		  , ("fnof",	402)
		  , ("Alpha",	913)
		  , ("Beta",	914)
		  , ("Gamma",	915)
		  , ("Delta",	916)
		  , ("Epsilon",	917)
		  , ("Zeta",	918)
		  , ("Eta",	919)
		  , ("Theta",	920)
		  , ("Iota",	921)
		  , ("Kappa",	922)
		  , ("Lambda",	923)
		  , ("Mu",	924)
		  , ("Nu",	925)
		  , ("Xi",	926)
		  , ("Omicron",	927)
		  , ("Pi",	928)
		  , ("Rho",	929)
		  , ("Sigma",	931)
		  , ("Tau",	932)
		  , ("Upsilon",	933)
		  , ("Phi",	934)
		  , ("Chi",	935)
		  , ("Psi",	936)
		  , ("Omega",	937)
		  , ("alpha",	945)
		  , ("beta",	946)
		  , ("gamma",	947)
		  , ("delta",	948)
		  , ("epsilon",	949)
		  , ("zeta",	950)
		  , ("eta",	951)
		  , ("theta",	952)
		  , ("iota",	953)
		  , ("kappa",	954)
		  , ("lambda",	955)
		  , ("mu",	956)
		  , ("nu",	957)
		  , ("xi",	958)
		  , ("omicron",	959)
		  , ("pi",	960)
		  , ("rho",	961)
		  , ("sigmaf",	962)
		  , ("sigma",	963)
		  , ("tau",	964)
		  , ("upsilon",	965)
		  , ("phi",	966)
		  , ("chi",	967)
		  , ("psi",	968)
		  , ("omega",	969)
		  , ("thetasym",	977)
		  , ("upsih",	978)
		  , ("piv",	982)
		  , ("bull",	8226)
		  , ("hellip",	8230)
		  , ("prime",	8242)
		  , ("Prime",	8243)
		  , ("oline",	8254)
		  , ("frasl",	8260)
		  , ("weierp",	8472)
		  , ("image",	8465)
		  , ("real",	8476)
		  , ("trade",	8482)
		  , ("alefsym",	8501)
		  , ("larr",	8592)
		  , ("uarr",	8593)
		  , ("rarr",	8594)
		  , ("darr",	8595)
		  , ("harr",	8596)
		  , ("crarr",	8629)
		  , ("lArr",	8656)
		  , ("uArr",	8657)
		  , ("rArr",	8658)
		  , ("dArr",	8659)
		  , ("hArr",	8660)
		  , ("forall",	8704)
		  , ("part",	8706)
		  , ("exist",	8707)
		  , ("empty",	8709)
		  , ("nabla",	8711)
		  , ("isin",	8712)
		  , ("notin",	8713)
		  , ("ni",	8715)
		  , ("prod",	8719)
		  , ("sum",	8721)
		  , ("minus",	8722)
		  , ("lowast",	8727)
		  , ("radic",	8730)
		  , ("prop",	8733)
		  , ("infin",	8734)
		  , ("ang",	8736)
		  , ("and",	8743)
		  , ("or",	8744)
		  , ("cap",	8745)
		  , ("cup",	8746)
		  , ("int",	8747)
		  , ("there4",	8756)
		  , ("sim",	8764)
		  , ("cong",	8773)
		  , ("asymp",	8776)
		  , ("ne",	8800)
		  , ("equiv",	8801)
		  , ("le",	8804)
		  , ("ge",	8805)
		  , ("sub",	8834)
		  , ("sup",	8835)
		  , ("nsub",	8836)
		  , ("sube",	8838)
		  , ("supe",	8839)
		  , ("oplus",	8853)
		  , ("otimes",	8855)
		  , ("perp",	8869)
		  , ("sdot",	8901)
		  , ("lceil",	8968)
		  , ("rceil",	8969)
		  , ("lfloor",	8970)
		  , ("rfloor",	8971)
		  , ("lang",	9001)
		  , ("rang",	9002)
		  , ("loz",	9674)
		  , ("spades",	9824)
		  , ("clubs",	9827)
		  , ("hearts",	9829)
		  , ("diams",	9830)
		  ]
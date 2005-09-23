-- |
-- DTD processing function for
-- including external parts of a DTD
-- parameter entity substitution and general entity substitution
--
-- Version : $Id$

module Text.XML.HXT.Parser.DTDProcessing
    ( getWellformedDoc
    , checkWellformedDoc
    , processDTD
    , processGeneralEntities
    )
where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.Parser.XmlOutput
    ( traceTree
    , traceSource
    , traceMsg
    )

import Text.XML.HXT.Parser.XmlParser
    ( parseXmlDoc
    , parseXmlDTDPart
    , parseXmlDTDTokens
    , parseXmlEntityValue
    , parseXmlAttrListBody
    , parseXmlAttrValue
    , parseXmlContentSpec
    , parseXmlGeneralEntityValue
    )

import Text.XML.HXT.Parser.XmlInput
    ( getXmlContents
    , getXmlEntityContents
    , runInLocalURIContext
    , getBaseURI
    , setBaseURI
    , isStandaloneDocument
    )

import Text.XML.HXT.DOM.EditFilters
    ( transfCharRef
    , transfAllCharRef
    )

import Text.XML.HXT.DOM.Util
    ( stringToUpper
    , stringTrim
    )

import Text.XML.HXT.DOM.XmlState

import Data.Maybe

-- ------------------------------------------------------------
--
-- the "main" building blocks

-- |
-- monadic filter for reading, parsing and checking a wellformed document.
-- the input tree must consist of a root node with a source attribute
-- in its attribute list.
--
-- All attributes from the document root are copied into the system state,
-- and may be queried by the monadic filters, e.g. trace options.
--
-- Result is the single element list containing the well-formed document tree
-- or, in case of errors, the document root with an empty list as children
-- and attributes 'a_status' and 'a_module' for error level and the module,
-- where the error occured.
--
-- this is a shortcut for 'getXmlContent' .\>\> 'checkWellformedDoc'
--
-- example for a main program:
--
-- @
-- main =
--   run\' \$
--   do
--   res  \<- getWellformedDoc \$ newDocument \"myfile.xml\"
--   ...
-- @

getWellformedDoc	:: XmlStateFilter state
getWellformedDoc
    = setSystemParams
      .>>
      getXmlContents
      .>>
      checkWellformedDoc

-- |
-- parses a text node with 'parseXmlDoc', processes the DTD and general entities
-- and transforms all char references into characters

checkWellformedDoc		:: XmlStateFilter state
checkWellformedDoc
    = parseXmlDoc
      .>>
      (processDTD `whenM` hasOption a_process_dtd)
      .>>
      processGeneralEntities
      .>>
      liftMf transfAllCharRef


-- ------------------------------------------------------------
--

type Env		= [(String, XmlTree)]

type RecList		= [String]

type DTDState res	= XState Env res

type DTDStateFilter	= XmlTree -> DTDState XmlTrees

data DTDPart		= Internal
			| External
			  deriving (Eq)

-- ------------------------------------------------------------

-- |
-- a filter for DTD processing
--
-- inclusion of external parts of DTD,
-- parameter entity substitution
-- conditional section evaluation
--
-- input tree must represent a complete document including root node

processDTD		:: XmlStateFilter a
processDTD
    = runInLocalURIContext
         ( processRoot
	   .>>
	   traceTree
	   .>>
	   traceSource
	 )
      `whenM` ( isRoot .> getChildren )
      where

      processRoot	:: XmlStateFilter a
      processRoot t
	  = do
	    sequence_ . map (\ (a, ts) -> setSysParamTree a ts) . toTreel . getAttrl $ t
	    setSysParam a_standalone ""
	    ( traceMsg 1 ("processDTD: process parameter enitities")
	      .>>
	      liftMf (modifyChildren addDoctype)
	      .>>
	      processChildrenM substParamEntities
	      .>>
	      checkResult "in XML DTD processing"
	      ) `whenM` statusOk
	      $ t

      -- Adds an empty DOCTYPE node to document. Needed for documents without a DTD.
      -- Otherwise processor can not substitute predefined entities. If an xml declaration
      -- is present, the node is inserted after this node.
      addDoctype :: XmlSFilter
      addDoctype docChilds
          = if null doctype
            then if null xmlDecl
                 then [mkXDTDTree DOCTYPE [] []] ++ docChilds
                 else (head docChilds) : [mkXDTDTree DOCTYPE [] []] ++ (tail docChilds)
            else docChilds
            where
            doctype = isDoctype $$ docChilds
            xmlDecl = isPi t_xml $$ isXPi $$ docChilds


substParamEntities	:: XmlStateFilter a
substParamEntities
    = processParamEntities
      `whenM`
      isDoctype
      where

      processParamEntities	:: XmlStateFilter a
      processParamEntities t'
	  = do
	    -- process internal part of DTD with initial empty env for parameter entities
	    (dtdInt, envInt) <- processInt [] t'

	    -- process external part of DTD with resulting env from internal DTD
	    dtdExt <- runInLocalURIContext (processExt envInt) t'

	    -- merge predefined, internal and external part
	    trace 2 "substParamEntities: merge internal and external DTD parts"
	    return (replaceChildren (foldl1 mergeDTDs [predefDTDPart, dtdInt, dtdExt]) t')

      processInt env' n'
	  = do
	    trace 2 "substParamEntities: substitute parameter entities in internal DTD part"
	    chain' env' (substParamEntity Internal $$< getChildren n')

      processExt env' n'
	  = do
	    trace 2 "substParamEntities: process external part of DTD"
            extDtd <- processExternalDTD n'
	    trace 2 "substParamEntities: substitute parameter entities in external DTD part"
	    chain env' ( (substParamEntity External) $$< extDtd)

-- ------------------------------------------------------------
-- |
-- get the value of a parameter entity

getPEvalue	:: XmlFilter

-- external parameter entities must be parsed when
-- accessing the value, not when reading the external document
-- because the interpretation of the content depends
-- on the point where it is inserted
-- internal parameter entity: just take the children

getPEvalue n
    = ( isExternalParameterEntity
	.>
	getValue a_value
	.>
	parseXmlEntityValue True ("external parameter entity " ++ valueOfDTD a_name n)
      )
      `orElse`
      ( isInternalParameterEntity
	.>
	getChildren
      )
      $ n

-- ------------------------------------------------------------

getPEvalueText	:: XmlFilter
getPEvalueText
    = ( isExternalParameterEntity
	.>
	getDTDValue a_value				-- take the value attribute
      )
      `orElse`
      ( xmlTreesToText					-- make text node
	. ( isInternalParameterEntity
	    .>
	    getChildren					-- get pe value
	    .>
	    transfCharRef				-- substitute character refs
	  )
      )

-- ------------------------------------------------------------
-- |
-- substitute parameter entities

substPEvalue	:: DTDPart -> Env -> RecList -> XmlFilter

substPEvalue loc env rl (NTree (XDTD PEREF al) _)
    | loc == Internal
	= xerr ("a parameter entity reference of " ++ peName' ++ " occurs in the internal subset of the DTD")
    | alreadySubstituted
	= xerr ("recursive call of parameter entity substitution for: " ++ peName')
    | isNothing peVal
	= xerr ("parameter entity " ++ peName' ++ " not found")
    | otherwise
	= substPEvalue loc env (peName : rl) `o` getPEvalue $ fromJust peVal
    where
    peName
	= lookup1 a_peref al
    peName'
	= show peName
    peVal
	= lookup peName env
    alreadySubstituted
	= peName `elem` rl

substPEvalue _ _ _ n
    = [n]

-- ------------------------------------------------------------
-- |
-- the dtd parameter entity substitution filter
--
-- parameter loc determines the context of the substitution: internal or external

substParamEntity	:: DTDPart -> DTDStateFilter
							-- parameter entity definition
substParamEntity loc n@(NTree (XDTD PENTITY al) _cs)
    = do
      doubleDef <- entityDefined peName
      if doubleDef
	 then
	 issueWarn ("parameter entity " ++ show peName ++ " already defined") n
	 else
	 ( ifM isExternalParameterEntity
	       (runInLocalURIContext substExternalParamEntity)
               substInternalParamEntity
	 ) n
      where
      peName  = lookup1 a_name al

      substInternalParamEntity	:: DTDStateFilter
      substInternalParamEntity n'
	  = do
	    env <- getState
	    cl' <- liftF (substPEvalue loc env [] `o` getChildren) n'
	    addParamEntity peName cl' n'
	    return []

      substExternalParamEntity	:: DTDStateFilter
      substExternalParamEntity (NTree (XDTD PENTITY al') _cs')
	  = let
	    sysVal  = lookup1 k_system al'
	    in do
								-- create a root node
	       rl <- getXmlEntityContents			-- add the document source location
		     $ newDocument' ((a_source, sysVal) : al')	-- and read the content
								-- process content, if io succeeded
	       base <- getBaseURI
	       substContent base rl

      substExternalParamEntity _
	  = error "substExternalParamEntity called with illegal argument"

      substContent	:: String -> XmlTrees -> DTDState XmlTrees
      substContent base content
	  = if null content				-- content not found
	    then
	      addParamEntity peName (xtext "") n	-- insert dummy value in env
	    else
	      let
	      val = getChildren $$ content
	      in
	      if null (isXText $$ val)
	      then
	      issueErr "illegal external parameter entity value" n
	      else
	      let
	      al1 = addEntry a_value (showXText val) . addEntry a_url base $ al
	      pe = mkXDTDTree PENTITY al1 []
	      in
	      addParamEntity peName [] pe

								-- parameter entities in entity value
substParamEntity loc n@(NTree (XDTD ENTITY _al) _)
    = do
      env <- getState
      cs  <- liftF (getChildren .> substPEvalue loc env [] .> transfCharRef) n	-- ???
      return (replaceChildren cs n)

								-- parameter entity as DTD macro
substParamEntity loc n@(NTree (XDTD PEREF _al) _cs)
    = ( substParamEntityRef "DTD part" parseXmlDTDPart (substParamEntity loc)
      ) n
								-- parameter entities in content model
substParamEntity _loc n@(NTree (XDTD ELEMENT _al) _cs)
    = substPar'
      `whenM`
      deep isPeRef						-- substitute only if PEs in content modell
      $ n
      where
      substPar' n'
	  = do
	    trace    2 ("substParamEntity: in content modell of " ++ elemName)

	    cs' <- substpeInContent $$< getChildren n'		-- substitute all pe's
	    let n2 = head $ replaceChildren cs' n'
	    let n3 = mkXTextTree . xmlContentModelToString $ n2
	    r'  <- ( liftF (parseXmlContentSpec context)	-- convert to text and parse again
		     .>>
		     liftMf (addDTDAttr a_name elemName)		-- new tree with element name inserted
		     .>>
		     traceTree
		     .>>
		     traceSource
		   ) n3					
	    return r'
	  where
	  elemName	= valueOfDTD a_name n'
	  context	= ( "content model of element "
                            ++ elemName
			    ++ " after parameter substitution"
			  )

substParamEntity _loc n@(NTree (XDTD ATTLIST []) _cs)
    = do
      trace    2 "substParamEntity: in ATTLIST decl"
      attrl <- (traceTree
		.>>
		liftMf getChildren
		.>>
		substParamEntityRef "proper ATTLIST definition" parseXmlDTDTokens thisM
	       ) n
      let n' = mkXTextTree (xshow attrl)

      res <- ( traceTree
	       .>>
	       liftF (parseXmlAttrListBody False "in <!ATTLIST ...> declaration after parameter entity substitution")
	       .>>
	       traceTree
	     ) $ n'

      return res

substParamEntity _loc n@(NTree (XDTD ATTLIST _al) _cs)
    = return [n]

substParamEntity Internal n@(NTree (XDTD CONDSECT _) _)
    = do
      issueErr "conditional sections in internal part of the DTD is not allowed" n
      return []

substParamEntity External n@(NTree (XDTD CONDSECT _) (c1 : cs))
    = do
      trace 2 "substParamEntity: process conditional section"
      traceTree n

      env  <- getState
      cond <- liftF (substPEvalue External env []) c1	-- substitute parameter entities
      let strRes = ( stringToUpper			-- and normalize result string
		     . stringTrim
		     . xshow
		   ) cond
      action strRes
      where
      action str
	  | str == k_ignore				-- IGNORE
	      = return []

	  | str == k_include				-- INCLUDE
	      = ( liftF ( parseXmlDTDPart False "INCLUDE part of conditional section"
			  `when`
			  isXText
			)
		  .>>
		  substParamEntity External
		) $$< cs

	  | otherwise					-- error
	      = issueErr ( "conditional section with bad value: "
			   ++ show str ++ " ( " ++ xshow [c1]
			   ++ " ), "   ++ show k_include
			   ++ " or "   ++ show k_ignore
			   ++ " expected"
			 ) n

							-- remove comments from DTD
substParamEntity _loc n
    | (not . null . isXCmt) n
	= return []

substParamEntity _loc n					-- default: keep things unchanged
    = return [n]


-- ------------------------------------------------------------
-- |
-- parameter entity ref in attribute enumeration

substParamEntityRef		:: String ->
				   (Bool -> String -> XmlFilter) ->
				   DTDStateFilter ->
				   DTDStateFilter

substParamEntityRef context parser cont n@(NTree (XDTD PEREF al) _)
    = do
      peEnv   <- getState
      action (lookup peName peEnv)
      where
      peName  = lookup1 k_peref al
      action Nothing
	  = issueErr ("parameter entity " ++ show peName ++ " in " ++ context ++ " not found") n
      action (Just t)
	  = runExternal ( liftF ( parser isExt (context ++ " defined by parameter entity: " ++ peName)
				  `o`
				  getPEvalueText
				)
			  .>> cont
			) $ t
	    where
	    isExt = satisfies (getDTDValue k_system) t
	    base  = (showXText . getDTDValue a_url) t

	    runWithBase	:: String -> DTDStateFilter -> DTDStateFilter
	    runWithBase	b f
		= runInLocalURIContext
		  ( \ t' -> ( do
			      trace 2 ("substParamEntityRef: external param entity " ++ show peName)
			      setBaseURI b
			      f t'
			    )
		  )
	    runExternal :: DTDStateFilter -> DTDStateFilter
	    runExternal f
		| isExt     = runWithBase base f
		| otherwise = f

substParamEntityRef _ _ _ n
    = return [n]

-- ------------------------------------------------------------
-- |
-- substitute parameter entities in content spec for elements
-- extra check is required for validation:
-- the parmeter entitiey must form a legal part of a content modell

substpeInContent	:: DTDStateFilter

substpeInContent n@(NTree (XDTD PEREF al) _cs)
    = do
      peEnv <- getState
      action (lookup peName peEnv)
    where
    peName  = lookup1 k_peref al
    action Nothing
	= issueErr ("parameter entity " ++ show peName ++ " referenced in element content not found") n
    action (Just t)
	  = liftF getPEvalueText t

substpeInContent n@(NTree (XDTD CONTENT _al) cs)
    = do
      cs' <- substpeInContent $$< cs
      return $ replaceChildren cs' n

substpeInContent n
    = return [n]

-- ------------------------------------------------------------
-- |
-- entity defined test

entityDefined	:: String -> DTDState Bool
entityDefined name
    = do
      env <- getState
      return (isJust . lookup name $ env)

-- ------------------------------------------------------------
-- |
-- parse a text node and substitute all parameter entity references

addParamEntity	:: String -> XmlTrees -> DTDStateFilter
addParamEntity name val t
    = let
      val' = head $ replaceChildren val t
      in
      do
      -- env <- getState
      trace    2 ("addParamEntity: " ++ name)
      traceTree val'
      changeState $ addEntry name val'
      return []

-- ------------------------------------------------------------

processExternalDTD	:: XmlStateFilter a
processExternalDTD n@(NTree (XDTD DOCTYPE al) _dtd)
    | null sysVal
	= return []
    | otherwise
	= do
	  checkStandalone
	  dtdText    <- getXmlEntityContents $ newDocument sysVal

	  trace    2 ("processExternalDTD: parsing DTD part for " ++ show sysVal)

	  dtdContent <- liftF (parseXmlDTDPart True sysVal `o` getChildren) $$< dtdText

	  trace    2 ("processExternalDTD: parsing DTD part done")
	  traceTree $ mkRootTree [] dtdContent
	  return dtdContent
    where
    sysVal		= lookup1 k_system al
    checkStandalone	= do
			  _isAlone <- isStandaloneDocument
			  if False -- isAlone
			     then issueErr ("external DTD " ++ show sysVal ++ " specified for standalone document") n
			     else return []

processExternalDTD  _
    = return []

-- ------------------------------------------------------------
-- |
-- merge the external and the internal part of a DTD into one internal part.
-- parameter entity substitution should be made befor applying this filter
-- internal definitions shadow external ones
--
--
-- preliminary: no real merge is done

mergeDTDs	:: XmlTrees -> XmlTrees -> XmlTrees
mergeDTDs dtdInt dtdExt
    = dtdInt ++ (mergeDTDentry dtdInt $$ dtdExt)

mergeDTDentry	:: XmlTrees -> XmlFilter
mergeDTDentry dtdPart
    = none `when` found
      where
      filterList = map filterDTDNode dtdPart	-- construct the list of filters
      found      = cat filterList		-- concatenate the filters (set union)


filterDTDNode	:: XmlTree -> XmlFilter

filterDTDNode (NTree (XDTD dtdElem al) _)
    | dtdElem `elem` [ELEMENT, NOTATION, ENTITY]
	= filterElement
	  where
	  filterElement n@(NTree (XDTD dtdElem' al') _cl')
	      | dtdElem == dtdElem' &&
		lookup a_name al' == lookup a_name al
		  = [n]
	      | otherwise
		  = []
	  filterElement _
	      = []

filterDTDNode (NTree (XDTD ATTLIST al) _)
    = filterAttlist
      where
      filterAttlist n@(NTree (XDTD ATTLIST al') _cl')
	  | lookup a_name  al' == lookup a_name  al &&
	    lookup a_value al' == lookup a_value al
		= [n]
      filterAttlist _
	  = []

filterDTDNode _
    =  none

-- ------------------------------------------------------------

predefinedEntities	:: String
predefinedEntities
    = concat [ "<!ENTITY lt   '&#38;#60;'>"
	     , "<!ENTITY gt   '&#62;'>"
	     , "<!ENTITY amp  '&#38;#38;'>"
	     , "<!ENTITY apos '&#39;'>"
	     , "<!ENTITY quot '&#34;'>"
	     ]

predefDTDPart		:: XmlTrees
predefDTDPart
    = parseXmlDTDPart False "predefined entities" $ mkXTextTree predefinedEntities

-- ------------------------------------------------------------
--
-- 4.4 XML Processor Treatment of Entities and References

data GeContext
    = ReferenceInContent
    | ReferenceInAttributeValue
    | ReferenceInEntityValue
    -- or OccursInAttributeValue				-- not used during substitution but during validation
    -- or ReferenceInDTD					-- not used: syntax check detects errors

newtype GeEnv		= GeEnv [GeEntry]

type GeEntry		= (String, GeFct)

type GeFct		= GeContext -> RecList -> GeStateFilter

type GeState res	= XState GeEnv res

type GeStateFilter	= XmlTree -> GeState XmlTrees

-- ------------------------------------------------------------

-- |
-- substitution of general entities
--
-- input: a complete document tree including root node

processGeneralEntities	:: XmlStateFilter a
processGeneralEntities
    = ( traceMsg 1 "processGeneralEntities: collect and substitute general enities"
	.>>
	processEntities
	.>>
	checkResult "in general entity processing"
	.>>
	traceTree
	.>>
	traceSource
      )
      `whenM` statusOk
      where
      processEntities t'
	  = do
	    res <- chain initialEnv (processGeneralEntity ReferenceInContent [] $$< getChildren t')
	    return $ replaceChildren res t'
	    where
	    initialEnv = GeEnv []

-- ------------------------------------------------------------

processGeneralEntity	:: GeContext -> RecList -> GeStateFilter
processGeneralEntity cx rl n@(NTree (XDTD DOCTYPE _) dtdPart)
    = do
      res <- processGeneralEntity cx rl $$< dtdPart
      return $ replaceChildren res n

processGeneralEntity cx rl n@(NTree (XDTD ENTITY al) cl)
    | isIntern
	= do
	  trace 2 ("processGeneralEnity: general entity definition for " ++ show name)
	  value <- liftF (parseXmlGeneralEntityValue False ("general internal entity " ++ show name)) $ mkXTextTree text
	  res   <- processGeneralEntity ReferenceInEntityValue (name:rl) $$< value
	  insertEntity name (substInternal res)
    | isExtern
	= do
	  baseUri <- getBaseURI
	  insertEntity name (substExternalParsed1Time baseUri)

    | isUnparsed
	= do
	  trace 2 ("processGeneralEnity: unparsed entity definition for " ++ show name)
	  insertEntity name (substUnparsed [])
    where
    isUnparsed	= not isIntern && not isExtern
    isExtern	= not isIntern && not (hasEntry k_ndata al)
    isIntern	= not (hasEntry k_system al)

    name	= lookup1 a_name al
    sysVal	= lookup1 k_system al
    context	= addEntry a_source sysVal al

    text  	= xshow . transfCharRef $$ cl

    processExternalEntityContents	:: XmlTrees -> GeState XmlTrees
    processExternalEntityContents cl'
	| null cl'					-- reading content did not succeed
	    = return []
	| null txt'					-- something weird in entity content
	    = do
	      issueErr ("illegal external parsed entity value for entity " ++ show name) n
	      return []
	| otherwise					-- o.k.: parse the contents
	    = do
	      res' <- liftF (parseXmlGeneralEntityValue True ("external parsed entity " ++ show name)) $$< txt'
	      traceSource .>> traceTree $ mkRootTree (fromAttrl context) res'
	      return res'
	where
	txt' = (isXText `o` getChildren) $$ cl'

    insertEntity	:: String -> GeFct -> GeState XmlTrees
    insertEntity name' fct'
	= do
	  (GeEnv env') <- getState
	  case lookup name' env' of
	    Just _fct
		-> do
		   issueWarn ("entity " ++ show name ++ " already defined, repeated definition ignored") n
		   return []
            Nothing
		-> do
		   changeState $ addEntity name' fct' 
		   return $ this n

    addEntity		:: String -> GeFct -> GeEnv -> GeEnv
    addEntity name' fct' (GeEnv env')
	= GeEnv (addEntry name' fct' env')

    -- --------
    --
    -- 4.4 XML Processor Treatment of Entities and References

    substInternal	:: XmlTrees -> GeContext -> RecList -> GeStateFilter
    substInternal nl ReferenceInContent rl' _n'
	= included nl rl'

    substInternal nl ReferenceInAttributeValue rl' _n'
	= includedInLiteral nl rl'

    substInternal _nl ReferenceInEntityValue _rl n'
	= bypassed n'

    -- --------

    substExternalParsed1Time	:: String -> GeContext -> RecList -> GeStateFilter
    substExternalParsed1Time baseUri' cx' rl' n'
	= do
	  trace 2 ("substExternalParsed1Time: read and parse external parsed entity " ++ show name)
	  res  <- runInLocalURIContext getContents' $ newDocument' context
	  -- res' <- processExternalEntityContents res
	  changeState $ addEntity name (substExternalParsed res)
	  substExternalParsed res cx' rl' n' 
	  where
	  getContents'	:: GeStateFilter
	  getContents' t''
	      = do
		setBaseURI baseUri'
		rs' <- getXmlEntityContents t''
		processExternalEntityContents rs'


    substExternalParsed	:: XmlTrees -> GeContext -> RecList -> GeStateFilter
    substExternalParsed  nl ReferenceInContent rl' _n'
	= includedIfValidating nl rl'

    substExternalParsed _nl ReferenceInAttributeValue _rl _n'
	= forbidden "external parsed general" "in attribute value"

    substExternalParsed _nl ReferenceInEntityValue _rl n'
	= bypassed n'

    -- --------

    substUnparsed	:: XmlTrees -> GeContext -> RecList -> GeStateFilter
    substUnparsed _nl ReferenceInContent _rl _n'
	= forbidden "unparsed" "content"
    substUnparsed _nl ReferenceInAttributeValue _rl _n'
	= forbidden "unparsed" "attribute value"
    substUnparsed _nl ReferenceInEntityValue _rl _n'
	= forbidden "unparsed" "entity value"

    -- --------
							-- see XML 1.0 chapter:

    included nl	rl'					-- 4.4.2
	= processGeneralEntity cx (name:rl') $$< nl

    includedIfValidating				-- 4.4.3
	= included

    includedInLiteral					-- 4.4.5
	= included

    bypassed n'						-- 4.4.7
	= return $ this n'

    forbidden msg' cx'					-- 4.4.4
	= do
	  issueErr ("reference of " ++ msg' ++ show name ++ " forbidden in " ++ cx') n
          return []

							-- normalize default value in ATTLIST
processGeneralEntity _cx rl n@(NTree (XDTD ATTLIST al) _cl)
    | hasDefaultValue
	= do
	  res <- ( liftF (parseXmlAttrValue "default value of attribute ")
                   .>>
		   substGeneralEntityInAValue rl
		 ) $ mkXTextTree defaultValue
	  return $ addDTDAttr a_default (xshow res) n
    | otherwise
	= return $ this n
    where
    hasDefaultValue = hasEntry  a_default al
    defaultValue    = lookup1   a_default al

processGeneralEntity cx rl n@(NTree (XEntityRef name) _)
    = do
      trace 2 ("processGeneralEnity: entity reference for entity " ++ show name)
      trace 3 ("recursion list = " ++ show rl)
      (GeEnv env) <- getState
      case lookup name env of
        Just fct
	  -> if name `elem` rl
	     then do
		  issueErr ("recursive substitution of general entity reference " ++ show ref ++ " not processed") n
		  return nl
	     else do
		  fct cx rl n
        Nothing
	  -> do
	     issueErr ("general entity reference " ++ show ref ++ " not processed, no definition found, (forward reference?)") n
	     return nl
      where
      nl  = this n
      ref = xshow nl


processGeneralEntity cx rl n@(NTree (XTag _tagName al) cl)
    = do
      al' <- substGeneralEntityInAttr rl $$< al
      cl' <- processGeneralEntity cx rl  $$< cl
      return $ (replaceAttrl al' .> replaceChildren cl') n

processGeneralEntity _cx _rl n
    = return $ this n

-- ------------------------------------------------------------

substGeneralEntityInAttr	:: RecList -> XmlTree -> GeState XmlTrees
substGeneralEntityInAttr rl a@(NTree (XAttr _) aValue)
    = do
      nv <- substGeneralEntityInAValue rl $$< aValue
      return (replaceChildren nv a)

substGeneralEntityInAttr _ _
    = return []

substGeneralEntityInAValue	:: RecList -> GeStateFilter
substGeneralEntityInAValue rl
    = ( processGeneralEntity ReferenceInAttributeValue rl
	`whenM`
	isXEntityRef
      )
      .>>
      liftMf ( ( modifyText normalizeWhiteSpace `when` isXText)
	      .>
	      (transfCharRef `when` isXCharRef)
	    )
      where
      normalizeWhiteSpace
	  = map ( \c -> if c `elem` "\n\t\r" then ' ' else c )

-- ------------------------------------------------------------



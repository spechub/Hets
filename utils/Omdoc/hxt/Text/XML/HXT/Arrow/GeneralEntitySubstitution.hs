-- |
-- general entity substitution
--
-- version: $Id$

module Text.XML.HXT.Arrow.GeneralEntitySubstitution
    ( processGeneralEntities )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowState
import Control.Arrow.ArrowTree

import Control.Arrow.IOStateListArrow

import Text.XML.HXT.DOM.XmlKeywords
    ( a_default
    , a_name
    , a_source
    , k_ndata
    , k_system
    )

import Text.XML.HXT.DOM.TypeDefs

import Text.XML.HXT.Arrow.XmlArrow
import Text.XML.HXT.Arrow.XmlFilterInterface
    ( parseXmlAttrValue
    , parseXmlGeneralEntityValue
    , transfCharRef
    )
import Text.XML.HXT.Arrow.XmlIOStateArrow
import Text.XML.HXT.Arrow.DocumentInput
    ( getXmlEntityContents )

import Data.Maybe

-- ------------------------------------------------------------

data GEContext
    = ReferenceInContent
    | ReferenceInAttributeValue
    | ReferenceInEntityValue
    -- or OccursInAttributeValue				-- not used during substitution but during validation
    -- or ReferenceInDTD					-- not used: syntax check detects errors

newtype GEEnv		= GEEnv (AssocList String GESubstArrow)

type GESubstArrow	= GEContext -> RecList -> GEArrow XmlTree XmlTree

type GEArrow b c	= IOSLA (XIOS, GEEnv) b c

type RecList		= [String]

-- ------------------------------------------------------------

processGeneralEntities	:: IOSArrow XmlTree XmlTree
processGeneralEntities
    = ( traceMsg 1 "processGeneralEntities: collect and substitute general enities"
	>>>
	runSt (GEEnv []) (processChildren (processGeneralEntity ReferenceInContent []))
	>>>
	setDocumentStatusFromSystemState "in general entity processing"
	>>>
	traceTree
	>>>
	traceSource
      )
      `when`
      documentStatusOk

      
processGeneralEntity	:: GESubstArrow
processGeneralEntity context recl
    = choiceA [ isElem		:-> ( processAttrl (processChildren substEntitiesInAttrValue)
		                      >>>
		                      processChildren (processGeneralEntity context recl)
				    )
	      , isDTDDoctype	:-> processChildren (processGeneralEntity context recl)
	      , isDTDEntity	:-> addEntityDecl
	      , isDTDAttlist	:-> substEntitiesInAttrDefaultValue
	      , isEntityRef	:-> substEntityRef
	      , this 		:-> this
	      ]
    where
    addEntityDecl	:: GEArrow XmlTree XmlTree
    addEntityDecl
	= perform ( choiceA [ isIntern		:-> addInternalEntity		-- don't change sequence of cases
			    , isExtern		:-> addExternalEntity
			    , isUnparsed	:-> addUnparsedEntity
			    ]
		  )
	where
	isIntern	= none `when` hasDTDAttr k_system
	isExtern	= none `when` hasDTDAttr k_ndata
	isUnparsed	= this

    addInternalEntity	:: GEArrow XmlTree b
    addInternalEntity
	= ( ( getDTDAttrValue a_name
	      >>>
	      liftSt (traceString 2 (("processGeneralEntity: general entity definition for " ++) . show))
	    )
	    &&&
	    ( xshow ( getChildren
		      >>>
		      transfCharRef
		    )
	    )
	  )
          >>>
	  applyA ( arr2 $ \ entity str ->
		   listA ( liftSt ( txt str
				    >>>
				    parseXmlGeneralEntityValue False ("general internal entity" ++ show entity)
				    >>>
				    filterErrorMsg
				  )
			   >>>
			   processGeneralEntity ReferenceInEntityValue (entity : recl)
			 )
		   >>>
		   applyA (arr $ \ ts -> insertEntity (substInternal ts) entity)
		 )
	  >>>
	  none

    addExternalEntity	:: GEArrow XmlTree b
    addExternalEntity
	= ( ( getDTDAttrValue a_name
	      >>>
	      liftSt (traceString 2 (("processGeneralEntity: external entity definition for " ++) . show))
            )
	    &&&
	    getDTDAttrValue k_system
            &&&
	    liftSt getBaseURI
	  )
	  >>>
	  applyA (arr3 $ \ entity uri baseUri -> insertEntity (substExternalParsed1Time uri baseUri) entity)
	  >>>
	  none

    addUnparsedEntity	:: GEArrow XmlTree b
    addUnparsedEntity
	= getDTDAttrValue a_name
	  >>>
	  liftSt (traceString 2 (("processGeneralEntity: unparsed entity definition for " ++) . show))
          >>>
	  applyA (arr (insertEntity substUnparsed))
	  >>>
	  none

    insertEntity	:: (String -> GESubstArrow) -> String -> GEArrow b b
    insertEntity fct entity
	= ( getState
	    >>>
	    applyA (arr $ checkDefined . snd)
	  )
	  `guards`
	  addEntity fct entity
	where
	checkDefined (GEEnv env)
	    = maybe ok alreadyDefined . lookup entity $ env
	    where
	    ok	= this
	    alreadyDefined _
		= liftSt $
		  issueWarn ("entity " ++ show entity ++ " already defined, repeated definition ignored")

    addEntity	:: (String -> GESubstArrow) -> String -> GEArrow b b
    addEntity fct entity
	= changeState ins
	where
	ins (s1, GEEnv env) _x = (s1, GEEnv (addEntry entity (fct entity) env))

    substEntitiesInAttrDefaultValue	:: GEArrow XmlTree XmlTree
    substEntitiesInAttrDefaultValue
	= applyA ( xshow ( liftSt ( getDTDAttrValue a_default			-- parse the default value
				    >>>						-- substitute enities
				    mkText					-- and convert value into a string
				    >>>
				    parseXmlAttrValue "default value of attribute"
				    >>>
				    filterErrorMsg
				  )
			   >>>
			   substEntitiesInAttrValue
			 )
		   >>> arr (setDTDAttrValue a_default)
		 )
          `when` hasDTDAttr a_default

    substEntitiesInAttrValue	:: GEArrow XmlTree XmlTree
    substEntitiesInAttrValue
	= ( processGeneralEntity ReferenceInAttributeValue recl
	    `when`
	    isEntityRef
	  )
          >>>
	  changeText normalizeWhiteSpace
	  >>>
	  transfCharRef
	where
	normalizeWhiteSpace = map ( \c -> if c `elem` "\n\t\r" then ' ' else c )


    substEntityRef	:: GEArrow XmlTree XmlTree
    substEntityRef
	= applyA ( ( ( getEntityRef				-- get the entity name and the env
		       >>>					-- and compute the arrow to be applied
		       liftSt ( traceString 2 (("processGeneralEntity: entity reference for entity " ++) . show)
				>>>
				traceMsg 3 ("recursion list = " ++ show recl)
			      )
		     )
		     &&&
		     (getState >>> arr snd)
		   ) >>>
		   arr2 substA
		 )
	  `orElse` this
	  where
	  substA	:: String -> GEEnv -> GEArrow XmlTree XmlTree
	  substA entity (GEEnv env)
	      = maybe entityNotFound entityFound . lookup entity $ env
	      where
	      errMsg msg
		  = liftSt (issueErr msg)

	      entityNotFound
		  = errMsg ("general entity reference \"&" ++ show entity ++ ";\" not processed, no definition found, (forward reference?)")

	      entityFound fct
		  | entity `elem` recl
		      = errMsg ("general entity reference \"&" ++ show entity ++ ";\" not processed, no definition found, (forward reference?)")
		  | otherwise
		      = fct context recl

    substExternalParsed1Time				:: String -> String -> String -> GESubstArrow
    substExternalParsed1Time uri baseUri entity cx rl
 	= perform ( liftSt ( traceMsg 2 ("substExternalParsed1Time: read and parse external parsed entity " ++ show entity)
			     >>>
			     runInLocalURIContext ( constA baseUri >>> setBaseURI
						    >>>
						    root [sattr a_source uri] []
						    >>>
						    listA ( getXmlEntityContents
							    >>>
							    processExternalEntityContents
							  )
						  )
			   )
		    >>>
		    applyA ( arr $ \ ts -> addEntity (substExternalParsed ts) entity )
		  )
	  >>>
	  processGeneralEntity cx rl
	where
	processExternalEntityContents	:: IOSArrow XmlTree XmlTree
	processExternalEntityContents
	    = ( ( documentStatusOk				-- reading entity succeeded
		  >>>						-- with content stored in a text node
		  (getChildren >>> isText)
		)
		`guards`
		( getChildren
		  >>>
		  parseXmlGeneralEntityValue True ("external parsed entity " ++ show entity)
		  >>>
		  filterErrorMsg
		)
	      )
	      `orElse`
	      issueErr ("illegal value for external parsed entity " ++ show entity)

    substExternalParsed					:: XmlTrees -> String -> GESubstArrow
    substExternalParsed	ts entity ReferenceInContent rl	= includedIfValidating ts rl entity
    substExternalParsed	_  entity ReferenceInAttributeValue _
                                                        = forbidden entity "external parsed general" "in attribute value"
    substExternalParsed	_  _      ReferenceInEntityValue _
                                                        = bypassed

    substInternal					:: XmlTrees -> String -> GESubstArrow
    substInternal ts entity ReferenceInContent rl	= included          ts rl entity
    substInternal ts entity ReferenceInAttributeValue rl= includedInLiteral ts rl entity
    substInternal _  _      ReferenceInEntityValue _	= bypassed

    substUnparsed					:: String -> GESubstArrow
    substUnparsed entity ReferenceInContent        _	= forbidden entity "unparsed" "content"
    substUnparsed entity ReferenceInAttributeValue _	= forbidden entity "unparsed" "attribute value"
    substUnparsed entity ReferenceInEntityValue    _	= forbidden entity "unparsed" "entity value"

									-- XML 1.0 chapter 4.4.2
    included		:: XmlTrees -> RecList -> String -> GEArrow XmlTree XmlTree
    included ts rl entity
	= arrL (const ts)
	  >>>
	  processGeneralEntity context (entity : rl)

									-- XML 1.0 chapter 4.4.3
    includedIfValidating		:: XmlTrees -> RecList -> String -> GEArrow XmlTree XmlTree
    includedIfValidating
	= included

									-- XML 1.0 chapter 4.4.4
    forbidden		:: String -> String -> String -> GEArrow XmlTree XmlTree
    forbidden entity msg cx
 	= liftSt (issueErr ("reference of " ++ msg ++ show entity ++ " forbidden in " ++ cx))

									-- XML 1.0 chapter 4.4.5
    includedInLiteral		:: XmlTrees -> RecList -> String -> GEArrow XmlTree XmlTree
    includedInLiteral
	= included

									-- XML 1.0 chapter 4.4.7
    bypassed		:: GEArrow XmlTree XmlTree
    bypassed
	= this

-- ------------------------------------------------------------

-- ------------------------------------------------------------

{- |
   Module     : Text.XML.HXT.Arrow.Namespace
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt (uwe\@fh-wedel.de)
   Stability  : experimental
   Portability: portable
   Version    : $Id$

   namespace specific arrows

-}

-- ------------------------------------------------------------

module Text.XML.HXT.Arrow.Namespace
    ( NsEnv
    , isNamespaceDeclAttr
    , getNamespaceDecl
    , processWithNsEnv
    , propagateNamespaces
    , validateNamespaces
    )
where

import Control.Arrow				-- arrow classes
import Control.Arrow.ArrowList
import Control.Arrow.ArrowIf
import Control.Arrow.ArrowTree
import Control.Arrow.ListArrow

import Text.XML.HXT.DOM.NamespacePredicates
import Text.XML.HXT.DOM.TypeDefs
import Text.XML.HXT.DOM.Util		( doubles )
import Text.XML.HXT.DOM.XmlKeywords

import Text.XML.HXT.Arrow.XmlArrow

-- ------------------------------------------------------------

-- | test whether an attribute node contains an XML Namespace declaration

isNamespaceDeclAttr	:: ArrowXml a => a XmlTree XmlTree
isNamespaceDeclAttr
    = (getAttrName >>> isA isNsQName) `guards` this
      where
      isNsQName n
	  = px == a_xmlns
	    &&
	    (null lp || (not . null . tail $ lp))
	  where
	  (px, lp) = span (/= ':') . qualifiedName $ n

-- | get the namespace prefix and the namespace URI out of
-- an attribute tree with a namespace declaration (see 'isNamespaceDeclAttr')
-- for all other nodes this arrow fails

getNamespaceDecl	:: ArrowXml a => a XmlTree (String, String)
getNamespaceDecl
    = isNamespaceDeclAttr
      >>>
      ( ( getAttrName
	  >>>
	  arr getNsPrefix
	)
	&&& xshow getChildren
      )
      where
      getNsPrefix = drop 6 . qualifiedName	-- drop "xmlns:"

-- ------------------------------------------------------------

-- | process a document tree with an arrow, containing always the
-- valid namespace environment as extra parameter.
-- The namespace environment is implemented as an 'Data.AssocList'

processWithNsEnv	:: ArrowXml a => (NsEnv -> a XmlTree XmlTree) -> NsEnv -> a XmlTree XmlTree
processWithNsEnv f env
    = ifA isElem						-- the test is just an optimization
      ( processWithExtendedEnv $< arr (extendEnv env) )		-- only element nodes contain namespace declarations
      ( processWithExtendedEnv env )
    where
    processWithExtendedEnv env'
	= f env'						-- apply the env filter
	  >>>
	  ( processAttrl (f env')				-- apply the env to all attributes
	    >>>
	    processChildren (processWithNsEnv f env')		-- apply the env recursively to all children
	  )
          `when` isElem						-- attrl and children only need processing for elem nodes

    extendEnv	:: NsEnv -> XmlTree -> NsEnv
    extendEnv env' t'
	= addEntries newDecls env'
	where
	newDecls = runLA ( getAttrl >>> getNamespaceDecl ) t'

-- -----------------------------------------------------------------------------

-- |
-- propagate all namespace declarations \"xmlns:ns=...\" to all
-- tag and attribute nodes of a document.
--
-- This filter does not check for illegal use of namespaces.
-- The real work is done by 'propagateNamespaceEnv'.
--
-- The filter may be applied repeatedly if neccessary.

propagateNamespaces	:: ArrowXml a => a XmlTree XmlTree
propagateNamespaces	= fromLA $ propagateNamespaceEnv [ (a_xml, xmlNamespace), (a_xmlns, xmlnsNamespace) ]

-- |
-- attaches the namespace info given by the namespace table
-- to a tag node and its attributes and children.

propagateNamespaceEnv	:: NsEnv -> LA XmlTree XmlTree
propagateNamespaceEnv
    = processWithNsEnv addNamespaceUri
    where
    addNamespaceUri	:: NsEnv -> LA XmlTree XmlTree
    addNamespaceUri env'
	= choiceA [ isElem :-> changeElemName (setNamespace env')
		  , isAttr :-> attachNamespaceUriToAttr env'
		  , this   :-> this
		  ]

    attachNamespaceUriToAttr	:: NsEnv -> LA XmlTree XmlTree
    attachNamespaceUriToAttr attrEnv
	= ( ( getName >>> isA hasPrefixLocalPart )
	    `guards`
	    changeAttrName (setNamespace attrEnv)
	  )
          `orElse`
	  ( changeAttrName (const xmlnsQN)
	    `when`
	    hasName a_xmlns
	  )
	where
	hasPrefixLocalPart	:: String -> Bool
	hasPrefixLocalPart s
	    = ( ':' `elem` s )				-- small optimization: only do some string handling when is ':' found
	      &&
	      ( let					-- check none empty prefix and local part
		(px, lp) = span (/= ':') s
		in
		not (null px) && not (null (drop 1 lp))
	      )

-- -----------------------------------------------------------------------------

-- |
-- validate the namespace constraints in a whole tree.
-- result is the list of errors concerning namespaces.
-- Work is done by applying 'validate1Namespaces' to all nodes.
-- Predicates 'isWellformedQName', 'isWellformedQualifiedName', 'isDeclaredNamespaces'
-- and 'isWellformedNSDecl' are applied to the appropriate tags and attributes.

validateNamespaces	:: ArrowXml a => a XmlTree XmlTree
validateNamespaces	= fromLA validateNamespaces1

validateNamespaces1	:: LA XmlTree XmlTree
validateNamespaces1
    = choiceA [ isRoot	:-> ( getChildren >>> validateNamespaces1 )		-- root is correct by definition
	      , this	:-> multi validate1Namespaces
	      ]

-- |
-- a single node for namespace constrains.

validate1Namespaces	:: LA XmlTree XmlTree
validate1Namespaces
    = choiceA
      [ isElem	:-> catA [ ( getQName >>> isA ( not . isWellformedQName )
			   )
			   `guards` nsError (\ n -> "element name " ++ show n ++ " is not a wellformed qualified name" )

			 , ( getQName >>> isA ( not . isDeclaredNamespace )
			   )
			   `guards` nsError (\ n -> "namespace for prefix in element name " ++ show n ++ " is undefined" )

		         , doubleOcc $< ( (getAttrl >>> getUniversalName) >>. doubles )

			 , getAttrl >>> validate1Namespaces
		         ]

      , isAttr	:-> catA [ ( getQName >>> isA ( not . isWellformedQName )
			   )
			   `guards` nsError (\ n -> "attribute name " ++ show n ++ " is not a wellformed qualified name" )

			 , ( getQName >>> isA ( not . isDeclaredNamespace )
			   )
			   `guards` nsError (\ n -> "namespace for prefix in attribute name " ++ show n ++ " is undefined" )

			 , ( hasNamePrefix a_xmlns >>> xshow getChildren >>> isA null
			   )
			   `guards` nsError (\ n -> "namespace value of namespace declaration for " ++ show n ++ " has no value" )

                         , ( getQName >>> isA (not . isWellformedNSDecl )
			   )
			   `guards`  nsError (\ n -> "illegal namespace declaration for name " ++ n ++ " starting with reserved prefix " ++ show "xml" )
			 ]

      , isDTD	:-> catA [ isDTDDoctype <+> isDTDAttlist <+> isDTDElement <+> isDTDName
		           >>>
			   getDTDAttrValue a_name
			   >>>
			   ( isA (not . isWellformedQualifiedName)
			     `guards`
			     nsErr (\ n -> "a DTD part contains a not wellformed qualified Name: " ++ show n)
			   )

			 , isDTDAttlist
			   >>>
			   getDTDAttrValue a_value
			   >>>
			   ( isA (not . isWellformedQualifiedName)
			     `guards`
			     nsErr (\ n -> "an ATTLIST declaration contains as attribute name a not wellformed qualified Name: " ++ show n)
			   )

                         , isDTDEntity <+> isDTDPEntity <+> isDTDNotation
			   >>>
			   getDTDAttrValue a_name
			   >>>
			   ( isA (not . isNCName)
                             `guards`
			     nsErr (\ n -> "an entity or notation declaration contains a not wellformed NCName: " ++ show n)
			   )
			 ]
      , isPi	:-> catA [ getName
		           >>>
			   ( isA (not . isNCName)
			     `guards`
			     nsErr (\ n -> "a PI contains a not wellformed NCName: " ++ show n)
			   )
			 ]
      ]
    where
    nsError	:: (String -> String) -> LA XmlTree XmlTree
    nsError msg
	= getName >>> nsErr msg

    nsErr	:: (String -> String) -> LA String XmlTree
    nsErr msg	= arr msg >>> mkError c_err

    doubleOcc	:: String -> LA XmlTree XmlTree
    doubleOcc an
	= nsError (\ n -> "multiple occurences of universal name for attributes of tag " ++ show n ++ " : " ++ show an )

-- ------------------------------------------------------------

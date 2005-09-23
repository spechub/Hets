-- |
-- Namespace filter
--
-- $Id$
--
-- Namespaces are processed with two main filter, 'propagateNamespaces'
-- and 'validateNamespaces'.
--
-- 'propagateNamespaces' takes a XML tree and
-- attaches extra namespace info at every tag name and attribute name.
-- So after processing a tree with 'propagateNamespaces', the access functions
-- "namespaceOf" and "universalNameOf" deliver the associated namespace (or \"\")
-- for tag names and attribute names.
--
-- 'validateNamespaces' checks whether names are wellformed related to the XML namespace definition.
-- whether a legal namespace is declared for all prefixes, and whether attribute names are unique
-- related to universal names.

module Text.XML.HXT.DOM.NamespaceFilter
    ( module Text.XML.HXT.DOM.NamespaceFilter
    )
where

import Text.XML.HXT.DOM.XmlTree

import Text.XML.HXT.DOM.Unicode
    ( isXmlNCNameStartChar
    , isXmlNCNameChar
    )

import Text.XML.HXT.DOM.Util
    ( doubles )

-- -----------------------------------------------------------------------------
--

-- |
-- Type for the namespace association list, used when propagating namespaces by
-- modifying the 'QName' values in a tree

type NamespaceTable = AssocList String String

-- -----------------------------------------------------------------------------
--

-- |
-- Compute the name prefix and the namespace uri for a qualified name.
--
-- This function does not test whether the name is a wellformed qualified name.
-- see Namespaces in XML Rule [6] to [8]. Error checking is done with separate functions,
-- see 'isWellformedQName' and 'isWellformedQualifiedName' for error checking.

setNamespace	:: NamespaceTable -> QName -> QName
setNamespace nst n
    = uncurry ns . span (/= ':') $ qn
    where
    qn = qualifiedName n	-- using qualifiedName instead of localPart enables recomputing of setNamespace

    ns :: String -> String -> QName
    ns lp ""					-- no ":" found in name
	= QN { namePrefix   = ""		-- use default namespace uri
	     , localPart    = lp
	     , namespaceUri = lookup1 "" nst
	     }

    ns px@(_:_) (':' : lp@(_:_))		-- none empty prefix and none empty local part found
	= QN { namePrefix   = px
	     , localPart    = lp
	     , namespaceUri = lookup1 px nst
	     }

    ns _ _					-- not a legal qualified name, don't change name
	= n

-- -----------------------------------------------------------------------------
--

-- |
-- test for wellformed NCName, rule [4] XML Namespaces
-- predicate is used in filter 'valdateNamespaces'.

isNCName	:: String -> Bool
isNCName []
    = False
isNCName n
    = and ( zipWith ($)
	    (isXmlNCNameStartChar : repeat isXmlNCNameChar)
	    n
	  )

-- |
-- test for wellformed QName, rule [6] XML Namespaces
-- predicate is used in filter 'valdateNamespaces'.

isWellformedQualifiedName	:: String -> Bool
isWellformedQualifiedName s
    | null s
	= True
    | null lp
	= isNCName px
    | otherwise
	= isNCName px && isNCName (tail lp)
    where
    (px, lp) = span (/= ':') s

-- |
-- test for wellformed QName values.
-- A QName is wellformed, if the local part is a NCName, the namePrefix, if not empty, is also a NCName.
-- predicate is used in filter 'valdateNamespaces'.

isWellformedQName	:: QName -> Bool
isWellformedQName n
    = isNCName lp				-- rule [8] XML Namespaces
      &&
      ( null px					-- rule [6] XML Namespaces
	||
	isNCName px				-- rule [7] XML Namespaces
      )
    where
    px = namePrefix n
    lp = localPart n

-- |
-- test for a wellformed namespace declaration
-- all namespace prefixes starting with \"xml\" are reserved for XML related definitions.
-- predicate is used in filter 'valdateNamespaces'.

isWellformedNSDecl	:: QName -> Bool
isWellformedNSDecl n
    = null px
      ||
      px /= "xmlns"
      ||
      (take 3 lp) /= "xml"
    where
    lp = localPart  n
    px = namePrefix n

-- |
-- 
-- predicate is used in filter 'valdateNamespaces'.

isDeclaredNamespace	:: QName -> Bool
isDeclaredNamespace n
    | null px					-- no namespace used
	= True
    | px == "xmlns"				-- "xmlns" has no associated namespace uri
	= null ns
    | px == "xml"				-- "xml" has a predefiend namespace"
	= ns == xmlNamespace
    | otherwise					-- namespace values are not empty
	= (not . null) ns
    where
    px = namePrefix   n
    ns = namespaceUri n

-- -----------------------------------------------------------------------------
--

-- |
-- the predefined namespace uri for xml: \"http:\/\/www.w3.org\/XML\/1998\/namespaces\"

xmlNamespace	:: String
xmlNamespace	= "http://www.w3.org/XML/1998/namespaces"


-- |
-- propagate all namespace declarations \"xmlns:ns=...\" to all
-- tag and attribute nodes of a document.
--
-- This filter does not check for illegal use of namespaces.
-- The real work is done by 'propagateNamespaceEnv'.
--
-- The filter may be applied repeatedly if neccessary.

propagateNamespaces	:: XmlFilter
propagateNamespaces	= propagateNamespaceEnv [ ("xml", xmlNamespace), ("xmlns", "") ]

-- |
-- attaches the namespace info given by the namespace table
-- to a tag node and its attributes and children.

propagateNamespaceEnv	:: NamespaceTable -> XmlFilter
propagateNamespaceEnv env n
    = ( ( processAttr (attachNamespaceUrisToAttr newEnv)
	  .>
	  processChildren (propagateNamespaceEnv newEnv)
	  .>
	  modifyQName (setNamespace newEnv)
	)
	`when`
	isXTag
      )
      $ n
    where
    nsAttrs	= getAttrl				-- scan all attributes
		  .>
		  isOfAttr ( (\ (px, lp)
			     -> (px == "xmlns"		-- check for prefix or whole name is "xmlns"
				 &&
				 lp /= ":"		-- check for none empty local part, "xmlns:" is not a legal name
				)
			     )
			     . span (/= ':')		-- break the name into a pair ("prefix", ":localPart")
			     . aName			-- select attribute name
			   )
		  $ n
    nsDecl	= zip (map (drop 1			-- drop the ":", empty local part represents default name space
			    . snd			-- take the local part with leading ":"
			    . span (/= ':')		-- break it like above
			    . nameOf			-- select attribute name
			   ) nsAttrs)
		      (map (xshow
			    .
			    getChildren
			   ) nsAttrs)
    newEnv	= addEntries nsDecl env

    attachNamespaceUrisToAttr	:: NamespaceTable -> XmlFilter
    attachNamespaceUrisToAttr attrEnv
	= modifyQName (setNamespace attrEnv)
	  `when`
	  isOfAttr ( (\ (px, lp)
		      -> ( (not . null) px		-- prefix and local part must not be empty
			   &&
			   (not . null . drop 1) lp
			 )
		     )
		     . span (/= ':')			-- break the name into a pair ("prefix", ":localPart")
		     . aName				-- select attribute name
		   )

-- -----------------------------------------------------------------------------

-- |
-- validate the namespace constraints in a whole tree.
-- result is the list of errors concerning namespaces.
-- Work is done by applying 'validate1Namespaces' to all nodes.
-- Predicates 'isWellformedQName', 'isWellformedQualifiedName', 'isDeclaredNamespaces'
-- and 'isWellformedNSDecl' are applied to the appropriate tags and attributes.

validateNamespaces	:: XmlFilter
validateNamespaces
    = choice [ isRoot
               :-> getChildren .> validateNamespaces		-- root is correct by definition
	     , this
	       :-> multi validate1Namespaces
	     ]

-- |
-- a single node for namespace constrains.

validate1Namespaces	:: XmlFilter
validate1Namespaces
    = choice [ isXTag
	       :->
	       cat [ isOfTag ( not . isWellformedQName )
		     `guards`
		     (\ n -> err ("tag name " ++ show (nameOf n) ++ " is not a wellformed qualified name") n )

		   , isOfTag ( not . isDeclaredNamespace )
		     `guards`
		     (\ n -> err ("namespace for prefix in tag name " ++ show (nameOf n) ++ " is undefined") n )

                   , (\ n -> ( let
		               dbls = doubles ((map universalNameOf . getAttrl) n)
		               in
		               if null dbls
		               then none
                               else err ( "multiple occurences of universal names for attributes of tag "
					  ++ show (nameOf n)
					  ++ " : " ++ foldr1 (\ x y -> x ++ ", " ++ y) (map show dbls)
					)
			     ) $ n
		     )

		   , getAttrl .> validate1Namespaces
		   ]

	     , isXAttr
	       :->
	       cat [ isOfAttr ( not . isWellformedQName )
		     `guards`
		     (\ n -> err ("attribute name " ++ show (nameOf n) ++ " is not a wellformed qualified name") n )

		   , isOfAttr ( not . isDeclaredNamespace )
	             `guards`
		     (\ n -> err ("namespace for prefix in attribute name " ++ show (nameOf n) ++ " is undefined") n )

                   , ( hasPrefix "xmlns" .> neg (xmlTreesToText . getChildren) )
		     `guards`
		     (\ n -> err ("namespace value of namespace declaration for " ++ show (nameOf n) ++ " has no value") n )

                   , isOfAttr ( not . isWellformedNSDecl )
		     `guards`
		     (\ n -> err ("illegal namespace declaration with reserved prefix " ++ show (localPartOf n) ++ " starting with \"xml\"") n )
	           ]

             , isXDTD
	       :->
	       cat [ ( ( isDoctype +++ isAttlist +++ isElement +++ isDTDName )
		       .>
		       isOf ( not . isWellformedQualifiedName . valueOfDTD a_name )
		     )
		     `guards`
                     (\ n -> err ("a DTD part contains a not wellformed qualified Name: " ++ show (valueOfDTD a_name n)) n )

		   , ( isAttlist
		       .>
		       isOf ( not . isWellformedQualifiedName . valueOfDTD a_value )
		     )
		     `guards`
                     (\ n -> err ("an ATTLIST declaration contains as attribute name a not wellformed qualified Name: " ++ show (valueOfDTD a_value n)) n )

                   , ( ( isEntity +++ isParameterEntity +++ isNotation )
		       .>
		       isOf ( not . isNCName . valueOfDTD a_name )
		     )
                     `guards`
                     (\ n -> err ("an entity or notation declaration contains a not wellformed NCName: " ++ show (valueOfDTD a_name n)) n )
		   ]
             , isXPi
	       :->
	       ( isOf ( not . isNCName . nameOf )
	         `guards`
                 (\ n -> err ("a PI contains a not wellformed NCName: " ++ show (nameOf n)) n )
	       )
	     ]

-- -----------------------------------------------------------------------------

isNamespaceDecl	:: XmlFilter
isNamespaceDecl
    = isOfAttr xmlnsName
      where
      xmlnsName	:: AttrName -> Bool
      xmlnsName a
	  = px == "xmlns"
	    &&
	    ( null ln || head ln == ':')
	  where
	  (px, ln) = splitAt 5 . qualifiedName $ a

-- -----------------------------------------------------------------------------

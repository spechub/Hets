{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer.Core
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A Generic XML Serializer using HXT and the Generics package (SYB3). This new version of
-- GXS is based on type classes, and thus allows modular customization. More coming soon.
--
-- This is the core serializer, as such it is capable of doing very little, and needs propogating
-- with serialization rules. A set of basic rules can be found in Text.XML.Serializer.DefaultRules
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the 
-- GNU General Public License as published by the Free Software Foundation; either version 2 
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without 
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not, 
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Text.XML.Serializer.Core where

import Data.Generics2
import Data.Array hiding (inRange)
import qualified Data.Array as Array
import Data.Array.IArray (amap)
import Data.Char
import Data.DynamicMap
import Data.Dynamic
import Data.List
import Data.Maybe
import Text.XML.HXT.Parser
import Text.XML.HXT.Aliases
import Network.URI
import Text.XML.Serializer.Datatypes
import Control.Monad.State
import Debug.Trace as DB

traceOn = False
xmlTrace x = if traceOn then DB.trace x else id

-- | Derive an XML Constructor with the given element name
deriveXTypeElem :: (Data DictXMLData a) => String -> a -> XMLType
deriveXTypeElem n = deriveXMLTypePrim [n] (Elem occursOnce)

-- | Derive an XML Constructor with the given attribute name
deriveXTypeAttr :: (Data DictXMLData a) => String -> a -> XMLType
deriveXTypeAttr n = deriveXMLTypePrim [n] (Attr occursOnce)

{- | Derive an XML Constructor for a data-type using SYB3 to generate the rules. Will either be based on field labels if presents or
     on internal defaults of the type being serialized.
-}
deriveXMLType x = deriveXMLTypePrim names (Elem occursOnce) x
  where names = if (isAlgType $ dataTypeOf ctx x) then (map showConstr $ dataTypeConstrs $ dataTypeOf ctx x) else replicate (glength ctx x) "item"
        ctx = undefined::DictXMLData ()

-- FIXME : Make sure this set appropriate cardinality for list child terms as default
deriveXMLTypePrim :: (Data DictXMLData a) => [String] -> (String -> Maybe URI -> PartSchema) -> a -> XMLType
deriveXMLTypePrim names f (dt::d) = 
      xmlType { fieldSchema    = if (isAlgType $ dataTypeOf ctx dt) then fieldElems else (listArray (1,1) [[]])
              , elementNames   = names
--                , attributeNames = names
              , defaultSchema    = let l = map (\n -> f n (namespaceURIA dt)) names in
                                     case l of
                                       [] -> Nothing
                                       [x]  -> Just x
                                       y    -> Just $ Choice occursOnce y
 		, choiceIndex    = constrIndex $ toConstr ctx dt -- Should only be used at serialization
                }
  where fieldElems = let l = zipWith fieldConstr cons fields in
			     listArray (1, (length l)) l

        fields = map constrFields cons
        cons = dataTypeConstrs $ dataTypeOf ctx dt
        flength = glength ctx dt
        ctx = undefined::DictXMLData ()

        fieldConstr c fs = let t   = ((fromConstr ctx c) :: d)                   -- Build a dummy type from the Constructor
                               cts = gmapQ ctx (dataTypeOf ctx) t                -- Get the child types of the dummy constructor
                               maybeTycon = tycon $ dataTypeOf (undefined::NoCtx ()) (Just "")   -- Type constructor for Maybe
                               listTycon  = tycon $ dataTypeOf (undefined::NoCtx ()) (Just [""]) -- Type constructor for List
			       dss = gmapQ ctx (defaultSchema . toXMLTypeA) t in -- Get default Schemas for each child type
				     if (length fs < length dss) 
					then replicate (length dss) ChildDefault--map (fromMaybe (Elem (1<->1) "item" Nothing)) dss
				        else map (\(ct, fn) ->
                                                   -- If we've got a list or a maybe, then we need a different cardinality constraint
                                                   let o = if (tycon ct == maybeTycon) then occursMaybe else 
                                                           if (tycon ct == listTycon)  then occursAny   else
                                                              occursOnce in
                                                      Elem o fn {-(namespaceURIA q dt)-}Nothing) (zip cts fs)
					-- We should probably develop a more intelligent method, but will do for now.
				    
-- | Get all the possible XML Constructors of a particular type.
getXMLTypes :: Data DictXMLData a => a -> [XMLType]
getXMLTypes (x::a) = 
    let dt = dataTypeOf ctx x 
        ctx = undefined::DictXMLData () in
             if (isAlgType dt) then map toXMLTypeA ((map (fromConstr ctx) $ dataTypeConstrs dt)::[a])
                               else [toXMLTypeA x]
        

-----------------------------------------------------------------------------------------------------
-- The Serialization Type-Classes
-----------------------------------------------------------------------------------------------------

-- | The XMLData class is an extension of Data which allows customization of XML serialization.
class (Data DictXMLData a) => XMLData a where    
    xmlEncode :: DynamicMap -> a -> SerializeTree XmlFilter -- Custom encoder
    {-  Perform the default case for serialization, provided the given data-item is XMLData and Data and there are
        no field properties specified, hand control over to XMLData to perform serialization. If there *are* field
        properties serialize by running serialize on each sub-term via gmapQ and then use zipWith to wrap up each
        serialization in elements and attributes (via xmlWrap).

        Strategy for encoding should be;
        1) Use a custom XML encoder if present
        2) If an algebraic data-type with custom fields, use those for encoding.
        3) If an algebraic data-type with record field, use those for encoding as element names.
        4) Use the default instance (atm via Show, but should be via SYB generic)
    -}
    xmlEncode dm x  = construct $ [SLeaf $ xmlWrap nst nsScope (Sequence occursOnce fs) [SNode $ gmapQ ctx (xmlEncodeA dm') x]]

      where ctx = undefined::DictXMLData ()
            fs  = (replicate (extensions xmlCons) (AnyElement (1<->1) AnyNS)) ++ fs'
            fs'  = zipWith3  (\s xc ns -> case s of
			                     ChildDefault -> getDefaultSchema xc ns
                                             x -> x) (getConsSchema xmlCons) xmlConstrs subNSs
            nst = lookupDM_D nstIKey dm
            ns  = namespaceURIA x
	    construct = if ((length $ dataTypeConstrs $ dataTypeOf ctx x) > 1) then ((:[]) . SIndex (choiceIndex xmlCons)) else id
            prefix = maybe "" (\ns -> fromMaybe "" $ lookup ns nst) ns
	    xmlConstrs = gmapQ ctx toXMLTypeA x
            subNSs = gmapQ ctx namespaceURIA x
            xmlCons = toXMLType x
	    constrs = gmapQ ctx (toConstr ctx) x
	    nsScope = lookupDM_D nsScopeKey dm
	    -- FIXME: Currently, the namespace in scope is only replaced if the current namespace is Nothing. Is this correct?
            dm' = addToDM (if (isNothing ns) then nsScope else ns)  nsScopeKey dm 


    xmlDecode ::  ReadX a -- Monadic Decoder
    xmlDecode = xmlDecodeDefault (undefined::a)
    toXMLType :: a -> XMLType
    toXMLType x = xmlType -- deriveXMLType x

-- | The default decoder for algebraic data-types.
xmlDecodeDefault :: (XMLData a, Data DictXMLData a) => a -> ReadX a
xmlDecodeDefault (x::a) = 
    do s <- get
       let xc = toXMLTypeA x -- Get the XML Type
	   perms = ((map (fromConstr ctx) $ dataTypeConstrs $ dataTypeOf ctx x)::[a]) -- Get representations of the type for each constructor
           sxcs = map (gmapQ ctx (toXMLTypeA)) perms -- Get the XML Type for each constructor
           subNSs = map (gmapQ ctx (namespaceURIA)) perms -- Get the namespace for each constructor
 
       -- Get the constructor index (if applicable) and the particle to deserialize.
       (n,t) <- partIndex

       -- If no constructor index has been given default to 1.
       let n' = fromMaybe 1 n
       
       -- If possible, get the particle schema for the given constructor index.
       fs <- if (Array.inRange (bounds $ fieldSchema xc) n') then return $ (fieldSchema xc ! n')
	                                                     else mzero
       
       xmlTrace (show fs) $ return ()
       xmlTrace (show $ particles s) $ return ()

       -- -*- Fill in ChildDefaults with the default properties of the children -*-
       -- i.e. Use the particle schemas for this type, the XML types and namespaces for each term to fill in default schemas if requested with actual
       -- schemas. This is the key to polymorphism as we allow serialization data to be retrieved from the child type (which may be polymorphic) 
       -- instead of the type itself.
       let fs'  = zipWith3  (\s xc ns -> case s of
			        ChildDefault -> getDefaultSchema xc ns
                                x            -> x) fs (sxcs!!(n'-1)) (subNSs!!(n'-1))

       
       -- Expand the tree one level (assuming cardinality 1)

       -- FIXME: This should have a different DTree parser of elements and attributes and shouldn't use a Sequence to parse
       -- with, since attributes are not particles. Hmmm... maybe not a FIXME. FIXME: Is this a FIXME? ;p


       -- Prepare a single schema structure to parse the tree with, using interleaving or sequence depending on whether the types declares itself
       -- as being interleaved.       
       let struct = if (isInterleaved xc) 
		       then Inter occursOnce fs'
	               else Sequence occursOnce fs'
           
       xmlTrace (show struct) $ return ()

       -- Parse the Deserialization Tree using the schema we have acquired, iff raw data is present in the leading position,
       -- otherwise we assume that the deserialization is already parsed.
       ext <- if (null t) then return t
	                  else case (head t) of
				   SLeaf (e, a) -> put s{elements = e, attributes = a} >> parseDTree struct
                                   _            -> return t

       --DB.trace (show ext) $ return ()
       xmlTrace "done" $ return ()

       -- Prepare a function which will deserialize a single constructor.
       let desCons c = do put s{ fields = zip fs' (defaultValues xc ++ repeat Nothing)
                               , thisXMLType = xc, thisConstr = c, particles = ext }
			  fromConstrM ctx deserialize c

       -- If partIndex has been set by something further up the tree, use that for deserialization without backtracking.
       maybe 
         (msum $ map desCons cons)
	 (\n -> desCons (cons!!(n-1))) n

    -- If deserialization fails to complete and a default value if present, we can use that instead to populate the value.
    `mplus` (do s <- get
                x <- lift (defaultValue s)
                lift $ fromDynamic x)

  where ctx  = undefined :: DictXMLData ()
	cons = dataTypeConstrs $ dataTypeOf ctx x


        deserialize :: forall b . (Data DictXMLData b) => ReadX b
        deserialize = result
          where 


            result = do 
                        (f, v) <- nextField
			s     <- get		

                        p <- nextParticle                      
			
                        xmlTrace "======" $ return ()
                        xmlTrace (show $ particles s) $ return ()
                        xmlTrace (show p) $ return ()
                        xmlTrace "======" $ return ()

                        s <- get
                        let cons = toConstr ctx thisType
                            xc  = toXMLTypeA thisType
                            tc  = thisConstr s
                            txc = thisXMLType s
			
                        x <- newReadX s{defaultValue = v, particles = p} (xmlDecodeA)
			s <- get

                        return x

            (thisType::b) = thisTypeOf result
              where 
                thisTypeOf :: ReadX b -> b
                thisTypeOf = undefined 



-- | Get all the possible XMLTypes of a data-type (rather redundant now)
toXMLTypesA :: Data DictXMLData a => a -> [XMLType]
toXMLTypesA (x::a) = map toXMLTypeA ((map (fromConstr ctx) $ dataTypeConstrs $ dataTypeOf ctx x)::[a])
    where ctx = undefined::DictXMLData ()


-- | Get the XML Constructor when only the dictonary is available, also handles complex-content extensions.
toXMLTypeA :: forall a . Data DictXMLData a => a -> XMLType
toXMLTypeA (x::a) = 
    let sxc = gmapQ ctx toXMLTypeA ((fromConstr ctx $ head $ dataTypeConstrs $ dataTypeOf ctx x)::a)
        xcs = map (gmapQ ctx toXMLTypeA) ((map (fromConstr ctx) $ dataTypeConstrs $ dataTypeOf ctx x)::[a])
	ctx = undefined::DictXMLData ()
	con = toXMLTypeD (dict::DictXMLData a) x 
        exs = map getConsPartSchema $ take (extensions con) sxc in
	      con { fieldSchema = amap (exs ++) (fieldSchema con)}

-- | Get the default schema of a data-type.
defaultSchemaA :: Data DictXMLData a => a -> Maybe PartSchema
defaultSchemaA x = defaultSchema $ toXMLTypeA x

-- | Get the XML Encoder when only the dictionary is available.
xmlEncodeA :: Data DictXMLData a => DynamicMap -> a -> SerializeTree XmlFilter
xmlEncodeA dm (x::a) = xmlEncodeD (dict::DictXMLData a) dm x

-- | Get the XML Decoder when only the dictionary is available. 
xmlDecodeA :: forall a . Data DictXMLData a => ReadX a
xmlDecodeA = result
  where
    (result :: ReadX a)  = xmlDecodeD (dict::DictXMLData a)

-- | Get a namespace using the XMLData dictionary.
namespaceURIA :: Data DictXMLData a => a -> Maybe URI
namespaceURIA (x::a) = namespaceURID (xmlNSDict (dict::DictXMLData a)) x

-- | Get a list of child namespaces from the dictionary.
containsNamespacesA :: Data DictXMLData a => a -> [URI]
containsNamespacesA (x::a) = containsNamespacesD (xmlNSDict (dict::DictXMLData a)) x

-- | Get a default prefix from the dictionary.
defaultPrefixA :: Data DictXMLData a => a -> String
defaultPrefixA (x::a) = defaultPrefixD (xmlNSDict (dict::DictXMLData a)) x

-- | Get all the namespace URIs and prefixes of a particular type.
getURIs :: (Data DictXMLData a) => a -> [(String, Maybe URI)]
getURIs (x::a) = (defaultPrefixA x, namespaceURIA x) : map ((,) "".Just) (containsNamespacesA x) ++ gmapQ (undefined::DictXMLData ()) (\c -> (defaultPrefixA c, namespaceURIA c)) x


-- | The dictionary lookup for XMLData
instance (Data DictXMLData a, XMLData a, XMLNamespace a) => Sat (DictXMLData a) where
    dict = DictXMLData { xmlEncodeD   = \d -> \x -> let dm = d `unionDM` (setFlags $ toXMLType x) in
                                                        (xmlEncode dm x) 
		       , xmlDecodeD   = xmlDecode
                       , toXMLTypeD   = toXMLType
		       , xmlNSDict = dict
		       }

                        

-----------------------------------------------------------------------------------------------------
-- XML Utilities for Serialization
-----------------------------------------------------------------------------------------------------

-- | Use the namespace classes to recursively read off a namespace table.
getDataNST :: Data DictXMLData a => a -> [(String, URI)] -> [(String, URI)]
getDataNST x onst = 
    assign 0 $ nubBy (snds (==)) $ reverse $ sortBy (fsts compare) $ (++) onst $ (\x->[(k,v)|(k,Just v)<-x]) $ concat $ getURIs x : everyone ctx getURIs x 
    where
    ctx = undefined :: DictXMLData ()
    assign _ [] = []
    assign n (h@(p,ns):t) = if (null p) then ("tns"++show n,ns):(assign (n+1) t) else h:assign n t

snds f = \(_,x) -> \(_,y) -> f x y
fsts f = \(x,_) -> \(y,_) -> f x y



-----------------------------------------------------------------------------------------------------
-- Core Serialization functions
-----------------------------------------------------------------------------------------------------


{- | The main function; given a Serialization Hook a piece of data and a Flag indicating whether we should 
     encode namespaces, perform serialization.
-}
serializeXML x n = fst $ serializeAux x n

serializeAux :: Data DictXMLData a => a -> Bool -> (SerializeTree XmlFilter, DynamicMap)
serializeAux (x::a) n = (map (appendFilter (cat (namespaceTableFilter ns))) (xmlEncodeD (dict::DictXMLData a) dm x), dm)
   where dm   = addToDM ens nsScopeKey $ addToDM ns nstKey $ addToDM nstI nstIKey emptyDM
	 ens  = namespaceURIA x
         nstI = map swap ns
         ns   = if n then getDataNST x [] else []

-- | Perform serialization and apply the filters output to produce an actual list of trees.
toXML :: Data DictXMLData a => a -> Bool -> XmlTrees
toXML a b = let (s, dm) = serializeAux a b 
	        xc      = toXMLTypeA a
		n       = case s of
				[SIndex i _] -> if ((length $ elementNames xc) < i) then "root" else (elementNames xc)!!(i-1)
				_            -> (head $ elementNames xc) in
                                  toTrees (applyPrefixA dm a n) s -- FIXME : Rewrite to use serialize trees.

-- | Shortcut for serializing straight to a String.
toXMLString x n = xshow $ toXML x n


applyPrefixA dm x = let nst = lookupDM_D nstIKey dm; ns = namespaceURIA x; p = ns >>= \x -> lookup x nst in 
                              \x -> (maybe "" (\p -> p++":") p)++x


-- | Perform deserialization, take an XmlTrees and deserialize to a type.  
deserializeXML :: forall a . Data DictXMLData a => XmlTrees -> Maybe a
deserializeXML xml = result 
    where result :: Maybe a = runReadX s xmlDecodeA
           where nst = [ (p, ns) | (p, Just ns) <- map (\(p,ns)->(p,parseURIReference ns)) $ getNamespaceTable $ mkRootTree [] xml ]
 		 dm  = addToDM nst nstKey $ emptyDM
	 	 st = map getDTree xml
		 -- If the the top-level type has multiple element names, set an index in the tree.
		 getDTree t = maybe (SLeaf (getChildren t, getAttrl t))  
		              (\(i,_) -> SIndex i [SLeaf (getChildren t, getAttrl t)])
                              (if ((==) 1 $ length $ elementNames xc) 
                                 then Nothing
                                 else (find (\(n, l) -> not $ null $ hasLP l t) $ zip [1..] (elementNames xc))
			      )
		 s = RO undefined undefined [] st [] [] dm Nothing
		 xc = toXMLTypeA (undefined::a)
	  

-- | Shortcut for deserializing directly from a string. Do not use if you're XML file contains DTD or entities.
fromXMLString s = let xml = xparse $ mkRootTree [] $ xread s in deserializeXML xml

-- | A test function, given a type, perform a no-namespace serialization, deserialize it and see whether the same thing comes out.
{-testGXSReflection x = let des = (deserializeXML (head $ toTrees "" $ basicSerialize x)) in
				if ((Just x) == des) then Right () else Left ((show x) ++ " /= " ++ (show des))-}
		     
---------------------------------------------------------------------------------------------------------------------
-- ALIASES
---------------------------------------------------------------------------------------------------------------------

-- | Use Show to perform serialization of a simple type.
encodeViaShow :: (Show a, (Data DictXMLData a)) => DynamicMap -> a -> SerializeTree XmlFilter
encodeViaShow dm x = [SLeaf $ txt $ show x]

-- | Use Read to perform deserialization of a simple type.
decodeViaRead :: (Read a, (Data DictXMLData a)) => ReadX a
decodeViaRead = readText >>= \x -> (if (null x) then mzero else readM x)

readM :: (MonadPlus m, Read a) => String -> m a
readM s = let r = reads s in
    case r of
        [(x, "")] -> return x
        _         -> mzero 

-- | Wrap up a serialize tree using a type's default element schema.
wrapDefaultElement :: Data DictXMLData a => DynamicMap -> a -> SerializeTree XmlFilter -> XmlFilter
wrapDefaultElement dm x ts = let nst = lookupDM_D nstIKey dm
			         sc  = lookupDM_D nsScopeKey dm
				 ns  = namespaceURIA x
				 nm  = elementNames $ toXMLTypeA x                            
				 es  = Choice (1<->1) $ map (\n -> Elem (1<->1) n ns) nm in
				       xmlWrap nst sc es ts

{-# OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer.Encoders
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- Some default encoders for GXS. Includes mostly serializers for abstract types, such
-- as lists etc.
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

module Text.XML.Serializer.Encoders where

import Text.XML.Serializer.Core
import Text.XML.Serializer.Datatypes
import Text.XML.Serializer.Derive
import Text.XML.HXT.Parser
import Text.XML.HXT.DOM.Util
import Text.XML.HXT.Aliases
import Control.Monad
import Control.Monad.State
import Data.Generics2
import Data.Maybe
import Data.Dynamic
import Data.DynamicMap
import Data.Array hiding (inRange)
import Network.URI
import qualified Data.Array as Array
import Debug.Trace as DB

-- A note to the world - no it isn't nice to have to declare XSD Types here as we shouldn't depend on XSD. But I've no choice, the alternative is
-- to use a bizarre hook system which I tried in haifa previously, and was rather difficult to use.
$(derive [''QName])
xsdTypeKey = newDynamicKey "xsdTypeKey" (undefined::QName)

instance XMLNamespace XmlTree where
    containsNamespaces (NTree t s) = (case t of
			 	       XTag  (QN _ _ ns) as -> (maybe [] (:[]) (parseURIReference ns)) 
				                                ++ (concat $ map containsNamespaces as)
			               XPi   (QN _ _ ns) as -> (maybe [] (:[]) (parseURIReference ns)) 
				                                ++ (concat $ map containsNamespaces as)
				       XAttr (QN _ _ ns)    -> (maybe [] (:[]) (parseURIReference ns))
				       _                    -> []
				   ) ++ (concat $ map containsNamespaces s)
instance XMLNamespace DTDElem
instance XMLNamespace XNode

$(deriveData [''NTree, ''XNode])
$(derive [''AttrSet, ''ElemSet, ''DTDElem])

{-
instance XMLData XNode
instance XMLData XmlTree
instance XMLData DTDElem
instance XMLData XmlTrees where
    xmlEncode dm q x = let nst = map (\(p,ns) -> (p, show ns)) $ lookupDM_D nstKey dm in [SLeaf $ \f -> (applyNamespaceTable nst $$ x)]
    xmlDecode q = do s <- get
		     return $ concat $ map flattenDNode $ particles s
-}

instance XMLNamespace a => XMLNamespace (Maybe a) where
    namespaceURI x = x >>= namespaceURI
    defaultPrefix = maybe "" defaultPrefix

instance (Data DictXMLData a, Data DictXMLData (Maybe a)) => XMLData (Maybe a) where
    toXMLType x = xmlType { elementNames  = elementNames xc
                          , defaultSchema = liftM (setSchemaOccurs occursMaybe) $ defaultSchema xc
			  , fieldSchema   = fieldSchema xc
                          , xmlMetaData   = xmlMetaData xc
                          }
        where xc = toXMLTypeA (undefined::a)
    xmlEncode dm x = maybe [] (xmlEncodeA dm) x
    xmlDecode = do s <- get
		   if (null $ particles s) 
		        then mzero
                        else do x <- xmlDecodeA
                                return (Just x)
                  `mplus` do s <- get
                             (maybe (return Nothing) return (defaultValue s >>= fromDynamic))

instance XMLNamespace a => XMLNamespace [a] where
    namespaceURI x  = {-if (null x) then Nothing else-} namespaceURI (undefined::a) --(head x)
    containsNamespaces = concat . map containsNamespaces
    defaultPrefix x = {-if (null x) then "" else-} defaultPrefix (undefined::a)

-- FIXME : This needs adapting to work with attribute lists too, which are altogether different to element lists.
--instance XMLNamespace Char
--instance XMLData Char

instance (Data DictXMLData [a], Data DictXMLData a) => XMLData [a] where
    toXMLType x = if (typeOf x == typeOf "")
                     then deriveXTypeElem "string" x
                     else xmlType { elementNames  = elementNames xc
		                  , defaultSchema = liftM (setSchemaOccurs occursAny) $ defaultSchema xc 
                                  , xmlMetaData   = xmlMetaData xc }
      where xc = toXMLTypeA (undefined::a)
    -- Lists represent particle cardinality, as a the inner lists must be concatenated, since we assume that whatever is inside
    -- has cardinality 1
    xmlEncode dm x = maybe (concat $ map (xmlEncodeA dm) x) (\x -> [SLeaf $ txt $ stringEscapeXml x]) (cast x)
    xmlDecode = if (typeOf (undefined::a) == typeOf 'a') 
                   then readText >>= return . fromJust . cast
                   else (do s <- get
		            -- let ne = length (elements s); na = length (attribs s)		     
                            mapM (\p -> newReadX s{particles=[p]} xmlDecodeA) (particles s))
                      

{-    xmlEncode _ x = [SLeaf $ txt x]
    toXMLType     = deriveXTypeElem "string"
    xmlDecode     = readText-}


instance (XMLNamespace a, XMLNamespace b) => XMLNamespace (Either a b) where
    namespaceURI  = either namespaceURI namespaceURI
    defaultPrefix = either defaultPrefix defaultPrefix

instance (Data DictXMLData a, Data DictXMLData b, Data DictXMLData (Either a b)) => XMLData (Either a b) where
    toXMLType x = let l = (undefined::a); r = (undefined::b) in
                      (deriveXMLType x) { defaultSchema = do x <- defaultSchemaA l
					                     y <- defaultSchemaA r
                                                             return $ Choice occursOnce [x, y]    
                                        }
    xmlEncode dm x = [either (SIndex 1 . xmlEncodeA dm) (SIndex 2 . xmlEncodeA dm ) x]
    xmlDecode = do s <- get
                   if (null $ particles s) then mzero else return ()
		   case (head $ particles s) of
		         SIndex 1 t -> put s{particles = t} >> xmlDecodeA >>= return . Left
		         SIndex 2 t -> put s{particles = t} >> xmlDecodeA >>= return . Right
                         _ -> (xmlDecodeA >>= return . Right) `mplus` (xmlDecodeA >>= return . Left)

{-
instance XMLNamespace (Union a)
-- We don't actually ever serialize a value of type a:|:b, but we need to be able to prove it because of Dictionary constraints.
-- instance (XMLData h a, XMLData h b, XMLHook h (a :|: b), XMLNamespace (a :|: b)) => XMLData h (a :|: b)
instance (Data DictXMLData (Union a), ShowUnion DictXMLData a (SerializeTree XmlFilter), ReadUnion DictXMLData (StateT ReadXO Maybe) a, TypeIndexOf a, HMapOut (ToXMLConstr h) a XMLType) => XMLData h (Union a) where
    xmlEncode dm h x = [SIndex (unionIndex x) $ serializeUnion (undefined::DictXMLData h ()) (Just $ toDyn dm) x]
    xmlDecode h = let ctx = (undefined::DictXMLData h ()) in
                            do s <- get
                               (i, t) <- partIndex
			       put s{particles = t}
              		       maybe (deserializeUnion ctx) (\n -> deserializeUnionAt ctx n) i
    toXMLConstr q x = xmlConstr { elementNames  = if (length names /= length cons) then replicate (length cons) "choice"
				                                                   else names,
				  defaultSchema = Just $ Elem occursOnce "choice" Nothing,
				  fieldSchema   = 
				      let ctx = (undefined::DictXMLData h ())
				          fs  = concat $ map (elems . fieldSchema) cons in
				                     listArray (1,length fs) fs,
                                  choiceIndex = unionIndex x
				}
      where cons  = hMapOut (ToXMLConstr q) (undefined::a)
            names = concat $ map elementNames cons

instance Data (DictXMLData h) a => Serializer (DictXMLData h) a (SerializeTree XmlFilter) where
    serialize ctx dyn x = xmlEncodeD (dict::DictXMLData h a) (fromMaybe emptyDM (dyn >>= fromDynamic)) x

instance Data (DictXMLData h) a => Deserializer (DictXMLData h) (StateT ReadXO Maybe) a where
    deserialize ctx = xmlDecodeD (dict::DictXMLData h a)


instance XMLNamespace HNil
instance XMLNamespace (HCons a l)
instance XMLData HNil where
    xmlDecode _ = return HNil
instance (HExtend a e (HCons a e), XMLNamespace (HCons a e), HMapOut (HToXML h) e (SerializeTree XmlFilter), HMapOut (ToXMLConstr h) e XMLConstr) => XMLData (HCons a e) where
    xmlEncode dm q x = [SNode (hMapOut (HToXML q dm) x)]
    -- This code is mostly adapted from the Core data-type serialization function, except it using tail recursion rather than SYB.
    -- FIXME : Add defaulting to Sequences.
    xmlDecode   = do let xc = toXMLConstrA (undefined::a)
     
                     p <- nextParticle

                     
		    
                     let des = do  --(f, d) <- nextField
				  (n, t) <- partIndex

                      		  

			          let n' = fromMaybe 1 n

                                  fs <- if (Array.inRange (bounds $ fieldSchema xc) n') then return $ (fieldSchema xc ! n')
	                                                                                else return []
                    
                                  
                                  s <- get

                                   -- Expand the tree one level (assuming cardinality 1)
                                  ext <- if ((null t) || (null fs))
			                      then return t
  	                                      else case (head t) of
				                        SLeaf (e, a) -> put s{elements = e
									     , attributes = a} >> parseDTree (Sequence occursOnce fs)
                                                        _            -> return t
                                  xmlDecodeA

                     s <- get

                     h <- newReadX s{particles = p} (des :: ReadX a)


                     t <- xmlDecodeA :: ReadX e

                     return ((h .*. t) :: HCons a e)

    toXMLType     x = xmlConstr { elementNames  = if (length names /= length cons) then replicate (length cons) "sequence"
				                                                  else names,
				  defaultSchema = Just $ Elem occursOnce "sequence" Nothing,
				  fieldSchema   = 
				      let ctx = (undefined::DictXMLData h ())
				          fs  = concat $ map (elems . fieldSchema) cons in
				                     listArray (1,1) fs
				}
      where cons  = hMapOut (ToXMLType q) (undefined::HCons a e)
            names = concat $ map elementNames cons



data HToXML h = HToXML h DynamicMap

instance Data (DictXMLData h) a => Apply (HToXML h) a (SerializeTree XmlFilter) where
    apply (HToXML q dm) x = xmlEncodeA dm q x

data ToXMLConstr h = ToXMLConstr h

instance Data (DictXMLData h) a => Apply (ToXMLConstr h) a XMLConstr where
    apply (ToXMLConstr q) x = toXMLConstrA q x
-}

--instance XMLNamespace AttrSet
--instance XMLData AttrSet where
{-    xmlDecode = do s <- get
                   case (particles s) of
		       (SLeaf (_, as):_) -> return $ AttrSet $ map (\t -> (qnameOf t, xshow $ getChildren t)) as
		       _                 -> return $ AttrSet []

    xmlEncode dm (AttrSet l) = [SNode (map (\(q,t) -> [SLeaf $ qattr q (txt t)]) l)]-}

--instance XMLNamespace ElemSet
--instance XMLData ElemSet where
{-    xmlDecode = do s <- get
		   case (particles s) of
		       (SLeaf (es, _):_) -> return $ ElemSet $ map (\t -> (qnameOf t, xshow $ getChildren t)) es
		       _                 -> return $ ElemSet []
    xmlEncode dm (ElemSet l) = [SNode (map (\(q,t) -> [SLeaf $ qetag q += (txt t)]) l)]-}
					


instance XMLNamespace (a, b)
instance (Data (DictXMLData) (a, b), Data (DictXMLData) a, Data (DictXMLData) b) => XMLData (a, b) where
    xmlEncode dm (a, b) = [SNode [xmlEncodeA dm a, xmlEncodeA dm b]]

    xmlDecode = do s <- get
                   case (particles s) of
                     (SNode (x:y:_):_) -> do p1 <- newReadX s{particles=x} xmlDecodeA
                                             p2 <- newReadX s{particles=y} xmlDecodeA
                                             return (p1, p2)
                     _         -> mzero

instance XMLNamespace (a, b, c)
instance (Data (DictXMLData) (a, b, c), Data (DictXMLData) a, Data (DictXMLData) b, Data (DictXMLData) c) => XMLData (a, b, c) where
    xmlEncode dm (a, b, c) = [SNode [xmlEncodeA dm a, xmlEncodeA dm b, xmlEncodeA dm c]]

    xmlDecode = do s <- get
                   case (particles s) of
                     (SNode (x:y:z:_):_) -> do p1 <- newReadX s{particles=x} xmlDecodeA
                                               p2 <- newReadX s{particles=y} xmlDecodeA
                                               p3 <- newReadX s{particles=z} xmlDecodeA
                                               return (p1, p2, p3)
                     _         -> mzero

instance XMLNamespace (a, b, c, d)
instance (Data (DictXMLData) (a, b, c, d), Data (DictXMLData) a, Data (DictXMLData) b, Data (DictXMLData) c, Data (DictXMLData) d) => XMLData (a, b, c, d) where
    xmlEncode dm (a, b, c, d) = [SNode [xmlEncodeA dm a, xmlEncodeA dm b, xmlEncodeA dm c, xmlEncodeA dm d]]

    xmlDecode = do s <- get
                   case (particles s) of
                     (SNode (n1:n2:n3:n4:_):_) -> do p1 <- newReadX s{particles=n1} xmlDecodeA
                                                     p2 <- newReadX s{particles=n2} xmlDecodeA
                                                     p3 <- newReadX s{particles=n3} xmlDecodeA
                                                     p4 <- newReadX s{particles=n4} xmlDecodeA
                                                     return (p1, p2, p3, p4)
                     _         -> mzero


data U2 a b         = U21 a | U22 b deriving Show
data U3 a b c       = U31 a | U32 b | U33 c deriving Show
data U4 a b c d     = U41 a | U42 b | U43 c | U44 d deriving Show
data U5 a b c d e   = U51 a | U52 b | U53 c | U54 d | U55 e deriving Show
data U6 a b c d e f = U61 a | U62 b | U63 c | U64 d | U65 e | U66 f deriving Show

$(derive [''U2, ''U3, ''U4, ''U5, ''U6])

instance XMLNamespace (U2 a b)
instance (Data (DictXMLData) (U2 a  b), Data (DictXMLData) a, Data (DictXMLData) b) => XMLData (U2 a b) where
    xmlEncode dm (U21 a) = [SIndex 1 $ xmlEncodeA dm a]
    xmlEncode dm (U22 b) = [SIndex 2 $ xmlEncodeA dm b]

    xmlDecode = do s <- get
                   (i, t) <- partIndex
                   put s{particles = t}
                   (case i of
                        Just 1 -> xmlDecodeA >>= return . U21
                        Just 2 -> xmlDecodeA >>= return . U22
                        _      -> mzero) `mplus` (xmlDecodeA >>= return . U21)
                                         `mplus` (xmlDecodeA >>= return . U22)
    toXMLType (U21 _) = xmlType { choiceIndex = 1 }
    toXMLType (U22 _) = xmlType { choiceIndex = 2 }


instance XMLNamespace (U3 a b c)
instance (Data (DictXMLData) (U3 a  b c), 
          Data (DictXMLData) a, 
          Data (DictXMLData) b,
          Data (DictXMLData) c) => XMLData (U3 a b c) where
    xmlEncode dm (U31 a) = [SIndex 1 $ xmlEncodeA dm a]
    xmlEncode dm (U32 b) = [SIndex 2 $ xmlEncodeA dm b]
    xmlEncode dm (U33 b) = [SIndex 3 $ xmlEncodeA dm b]

    xmlDecode = do s <- get
                   (i, t) <- partIndex
                   put s{particles = t}
                   (case i of
                        Just 1 -> xmlDecodeA >>= return . U31
                        Just 2 -> xmlDecodeA >>= return . U32
                        Just 3 -> xmlDecodeA >>= return . U33
                        _      -> mzero) `mplus` (xmlDecodeA >>= return . U31)
                                         `mplus` (xmlDecodeA >>= return . U32)
                                         `mplus` (xmlDecodeA >>= return . U33)
    toXMLType (U31 _) = xmlType { choiceIndex = 1 }
    toXMLType (U32 _) = xmlType { choiceIndex = 2 }
    toXMLType (U33 _) = xmlType { choiceIndex = 3 }

instance XMLNamespace (U4 a b c d)
instance (Data (DictXMLData) (U4 a  b c d), 
          Data (DictXMLData) a, 
          Data (DictXMLData) b,
          Data (DictXMLData) c,
          Data (DictXMLData) d) => XMLData (U4 a b c d) where
    xmlEncode dm (U41 a) = [SIndex 1 $ xmlEncodeA dm a]
    xmlEncode dm (U42 b) = [SIndex 2 $ xmlEncodeA dm b]
    xmlEncode dm (U43 b) = [SIndex 3 $ xmlEncodeA dm b]
    xmlEncode dm (U44 b) = [SIndex 4 $ xmlEncodeA dm b]

    xmlDecode = do s <- get
                   (i, t) <- partIndex
                   put s{particles = t}
                   (case i of
                        Just 1 -> xmlDecodeA >>= return . U41
                        Just 2 -> xmlDecodeA >>= return . U42
                        Just 3 -> xmlDecodeA >>= return . U43
                        Just 4 -> xmlDecodeA >>= return . U44
                        _      -> mzero) `mplus` (xmlDecodeA >>= return . U41)
                                         `mplus` (xmlDecodeA >>= return . U42)
                                         `mplus` (xmlDecodeA >>= return . U43)
                                         `mplus` (xmlDecodeA >>= return . U44)
    toXMLType (U41 _) = xmlType { choiceIndex = 1 }
    toXMLType (U42 _) = xmlType { choiceIndex = 2 }
    toXMLType (U43 _) = xmlType { choiceIndex = 3 }
    toXMLType (U44 _) = xmlType { choiceIndex = 4 }

instance XMLNamespace (U5 a b c d e)
instance (Data (DictXMLData) (U5 a  b c d e), 
          Data (DictXMLData) a, 
          Data (DictXMLData) b,
          Data (DictXMLData) c,
          Data (DictXMLData) d,
          Data (DictXMLData) e) => XMLData (U5 a b c d e) where
    xmlEncode dm (U51 a) = [SIndex 1 $ xmlEncodeA dm a]
    xmlEncode dm (U52 b) = [SIndex 2 $ xmlEncodeA dm b]
    xmlEncode dm (U53 b) = [SIndex 3 $ xmlEncodeA dm b]
    xmlEncode dm (U54 b) = [SIndex 4 $ xmlEncodeA dm b]
    xmlEncode dm (U55 b) = [SIndex 5 $ xmlEncodeA dm b]

    xmlDecode = do s <- get
                   (i, t) <- partIndex
                   put s{particles = t}
                   (case i of
                        Just 1 -> xmlDecodeA >>= return . U51
                        Just 2 -> xmlDecodeA >>= return . U52
                        Just 3 -> xmlDecodeA >>= return . U53
                        Just 4 -> xmlDecodeA >>= return . U54
                        Just 5 -> xmlDecodeA >>= return . U55
                        _      -> mzero) `mplus` (xmlDecodeA >>= return . U51)
                                         `mplus` (xmlDecodeA >>= return . U52)
                                         `mplus` (xmlDecodeA >>= return . U53)
                                         `mplus` (xmlDecodeA >>= return . U54)
                                         `mplus` (xmlDecodeA >>= return . U55)
    toXMLType (U51 _) = xmlType { choiceIndex = 1 }
    toXMLType (U52 _) = xmlType { choiceIndex = 2 }
    toXMLType (U53 _) = xmlType { choiceIndex = 3 }
    toXMLType (U54 _) = xmlType { choiceIndex = 4 }
    toXMLType (U55 _) = xmlType { choiceIndex = 5 }

{-    toXMLConstr q x = xmlConstr { elementNames  = if (length names /= length cons) then replicate (length cons) "choice"
				                                                   else names,
				  defaultSchema = Just $ Elem occursOnce "choice" Nothing,
				  fieldSchema   = 
				      let ctx = (undefined::DictXMLData h ())
				          fs  = concat $ map (elems . fieldSchema) cons in
				                     listArray (1,length fs) fs,
                                  choiceIndex = unionIndex x
				}
      where cons  = hMapOut (ToXMLConstr q) (undefined::a)
            names = concat $ map elementNames cons-}

{-
instance XMLData Int where
    xmlEncode = encodeViaShow
    toXMLType = deriveXTypeElem "int"
    xmlDecode = decodeViaRead

instance XMLNamespace Int

data Thing = Thing (U2 [Int] Int) deriving Show

$(derive [''Thing])

instance XMLNamespace Thing
instance XMLData Thing where
    toXMLType _ = xmlType { fieldSchema = array (1, 1) [(1, [Choice occursOnce [Elem occursOnce "p1" Nothing, Elem occursOnce "p2" Nothing]])] }
-}
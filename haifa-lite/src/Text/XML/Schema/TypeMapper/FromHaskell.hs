{-# OPTIONS_GHC -fth -fglasgow-exts -fallow-undecidable-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Schema.TypeMapper.FromHaskell
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A basic schema type mapper from Haskell -> XML Schema. Allows types which have had
-- XMLData based serializers declared for them to have associated schemas created.
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
module Text.XML.Schema.TypeMapper.FromHaskell (buildXSD, (.+.), HNil) where

import Org.W3.N2001.XMLSchema as XSD
import Data.Array
import Text.XML.Serializer
import Data.Typeable
import Data.Generics2
import Text.XML.HXT.Parser
import Network.URI
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Debug.Trace as DB

import qualified Data.AbstractMap as Map
import Data.HashMap

data HCons h t = HCons h t

-- | Type list terminator
data HNil = HNil

-- | Type list constructor
(.+.) = HCons

infixr 9 .+.


-- | Given a URI namespace and a list of types to map, create a simple XML Schema. 
-- e.g. buildXSD myURI (undefined::MyType1 .+. undefined::MyType2 .+. HNil)
-- Types must have been xmlified first (via XMLData).
buildXSD :: BuildXmlSchema a => URI -> a -> Schema
buildXSD u x = let ?typeMap = buildTypeMap x xsdTypeMap
                   ?namespaceMap = buildNamespaceMap u x $ xsdNamespaceMap in buildXmlSchema u [] x

class BuildXmlSchema a where
  buildXmlSchema    :: (?typeMap      :: HashMap TypeRep [String]
                       ,?namespaceMap :: HashMap TypeRep URI) => URI -> [ComplexType] -> a -> Schema
  buildTypeMap      :: a -> (HashMap TypeRep [String] -> HashMap TypeRep [String])
  buildNamespaceMap :: URI -> a -> (HashMap TypeRep URI -> HashMap TypeRep URI)

instance (BuildXmlSchema rst, Data DictXMLData t) => BuildXmlSchema (HCons t rst) where  
  buildXmlSchema u cts (HCons h t) = buildXmlSchema u (cts++[toComplexType h]) t
  buildTypeMap (HCons h t)        = Map.put (typeOf h) [show $ typeOf h] . buildTypeMap t
  buildNamespaceMap u (HCons h t) = Map.put (typeOf h) u . buildNamespaceMap u t

instance BuildXmlSchema HNil where
  buildXmlSchema u cts _ = Schema cts (Just u)
  buildTypeMap _ = id
  buildNamespaceMap _ _ = id

toComplexType :: (?typeMap      :: HashMap TypeRep [String]
                 ,?namespaceMap :: HashMap TypeRep URI
                 ,Data DictXMLData a
                 ) =>  a -> ComplexType
toComplexType (x::a) = let ctx = undefined :: DictXMLData ()
                           ps = elems $ fieldSchema $ toXMLTypeA x
                           hs = map (gmapQ ctx typeOf) ((map (fromConstr ctx) $ dataTypeConstrs $ dataTypeOf ctx x)::[a])
                           ts = zipWith (zipWith fromPartSchema) hs ps 
                           st = if (isInterleaved $ toXMLTypeA x) 
                                    then U42 $ All Nothing Nothing Nothing Nothing [x | U51 x <- (head ts)]
                                    else if (length ts == 1)  
                                           then U44 $ (XSD.Sequence) Nothing Nothing (head ts)
                                           else U43 $ XSD.Choice Nothing Nothing (map (\t -> U54 $ (XSD.Sequence) Nothing Nothing t) ts) in
                                       ComplexType Nothing Nothing Nothing Nothing Nothing (Just $ show $ typeOf x) Nothing (U33 (st, []))

                     
fromPartSchema :: (?typeMap      :: HashMap TypeRep [String]
                  ,?namespaceMap :: HashMap TypeRep URI
                  ) => TypeRep -> PartSchema -> U5 Element Group Choice Sequence Any
fromPartSchema tr (Elem o n _) = U51 (simpleElement n t o)
  where t = do let tr' = if ((typeRepTyCon $ typeOf tr) == (typeRepTyCon $ typeOf "hello")) then (head $ typeRepArgs $ typeOf tr) else tr
               tn  <- Map.lookup tr' ?typeMap
               tns <- Map.lookup tr' ?namespaceMap
                              
               return (QN "" (head tn) (show tns))

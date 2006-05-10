{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances -fno-monomorphism-restriction #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Org.Xmlsoap.Schemas.Soap.Encoding
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- Equivelant data-types and mappers required for SOAP Encoding data-types
-- at http://schema.xmlsoap.org/soap/encoding. Notably SOAP Arrays and
-- XML Serializers for the same.
--
-- This is a work in progress.
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
module Org.Xmlsoap.Schemas.Soap.Encoding where

import Text.XML.HXT.Parser hiding (mkName)
import Text.XML.HXT.Aliases
import qualified Data.Array
import qualified Data.Ix

import Text.XML.Serializer
import Org.W3.N2001.XMLSchema hiding (Sequence)
import qualified Org.W3.N2001.XMLSchema_instance as XSI
import Control.Monad
import Control.Monad.State
import Data.Array.IArray
import Language.Haskell.TH
-- import Text.XML.Schema.Utils
-- import Data.Generics.Serializer
import Data.Maybe
import qualified Data.Map as Map
import Data.DynamicMap
import Data.Generics2
import Network.URI
-- import Text.XML.Schema.TypeMapper
import Data.List
import Debug.Trace as DB
thisNamespace = parseURI "http://schemas.xmlsoap.org/soap/encoding/"
tns = thisNamespace
prefix = "soapenc"

-- | Check whether a raw SOAP Envelope is valid, and propogate indexes if none are present.
ratifySOAPArray :: SOAPArrayRaw a -> Maybe (SOAPArrayRaw a)
ratifySOAPArray (SOAPArrayRaw x) = 
    if ((all $ ((<=1) . length)) checkList)
       then Just $ SOAPArrayRaw $ sortBy (\x y -> compare (soapArrayIndex x) (soapArrayIndex y)) salist
       else Nothing

  where checkList = groupBy (\x y -> (soapArrayIndex x) == (soapArrayIndex y)) $ filter (not . null . fromSAIndex . soapArrayIndex) x
        salist = if (all (null . fromSAIndex . soapArrayIndex) x)
	           then zipWith (\(SOAPArrayElement i e) n -> (SOAPArrayElement (SOAPArrayIndex [n]) e)) x [0..]
                   else x

-- | A wrapper type for types which can be serialized to SOAP Envelopes via SOAPArrayRep
data SOAPArray a = SOAPArray {fromSOAPArray::a}

instance Show a => Show (SOAPArray a) where show (SOAPArray x) = show x

-- | Any types which can be serialized to SOAP Arrays should instantiate this class.
class SOAPArrayRep r where
    -- | Convert a concrete data-type representation to a raw SOAP Envelope.
    repToSA :: r a -> SOAPArrayRaw a
    -- | Convert a raw SOAP Envelope to an actual data-type.
    saToRep :: SOAPArrayRaw a -> ReadX (r a)

instance XMLNamespace (Map.Map Int a)
instance SOAPArrayRep (Map.Map Int) where
    repToSA m = soapar $ map (\(i, x) -> soapae (soapai [i]) x) (Map.assocs m)
    saToRep (SOAPArrayRaw x) = do a <- mapM saToAssocs x
				  return (Map.fromList a)
      where saToAssocs e = case e of
			       SOAPArrayElement (SOAPArrayIndex [i]) x -> return (i, x)
			       _ -> mzero				      

-- | An n-dimensional index for a SOAPArray
data SOAPArrayIndex = SOAPArrayIndex {fromSAIndex :: [Int]} deriving (Eq, Show, Ord)

soapai = SOAPArrayIndex

instance Data DictXMLData (Map.Map Int a) => XMLData (Map.Map Int a)


instance XMLNamespace a => XMLNamespace (SOAPArray a) where namespaceURI (SOAPArray x) = namespaceURI x
instance (Data DictXMLData (SOAPArray (r a)), Data DictXMLData (SOAPArrayRaw a), SOAPArrayRep r, Data DictXMLData a, Data DictXMLData (SOAPArrayRaw a)) => XMLData (SOAPArray (r a)) where
    toXMLType x = xmlType { elementNames = ["Array"] }
    xmlEncode dm (SOAPArray x) = xmlEncodeA dm $ repToSA x
    xmlDecode = xmlDecodeA >>= lift . ratifySOAPArray >>= saToRep >>= return . SOAPArray
    
instance XMLNamespace SOAPArrayIndex where namespaceURI _ = tns
instance (Data DictXMLData SOAPArrayIndex, Data DictXMLData [Int]) => XMLData SOAPArrayIndex where
    xmlEncode dm (SOAPArrayIndex x) = encodeViaShow dm x
    xmlDecode = (decodeViaRead >>= return . SOAPArrayIndex) `mplus` (return $ SOAPArrayIndex [])

-- | An element of a SOAP Array, containing an index and an item.
data SOAPArrayElement a = SOAPArrayElement { soapArrayIndex   :: SOAPArrayIndex, 
		         		     soapArrayElement :: a } deriving Show

soapae = SOAPArrayElement

-- | A partially serialized SOAP Array, should be convertible from any types which the user would 
-- like to serialize as SOAP Arrays.
data SOAPArrayRaw a = SOAPArrayRaw [SOAPArrayElement a] deriving Show

soapar = SOAPArrayRaw

$(derive [''SOAPArrayElement, ''SOAPArrayRaw, ''SOAPArray, ''SOAPArrayIndex])
	
instance XMLNamespace a => XMLNamespace (SOAPArrayElement a) where
    namespaceURI (SOAPArrayElement _ x)  = namespaceURI x
    defaultPrefix (SOAPArrayElement _ x) = defaultPrefix x


-- FIXME: This is just plain wrong, we can't use defaulting, write custom serializers and deserializers.
-- Hmmmm, why did I write the above; using defaulting seems perfectly ok to me, certainly it works.
instance (Data DictXMLData (SOAPArrayElement a), Data DictXMLData a) 
    => XMLData (SOAPArrayElement a) where
    toXMLType x = xmlType { elementNames  = elementNames xc
			  , defaultSchema = liftM (setSchemaOccurs occursAny) $ defaultSchema xc 
			  , fieldSchema =  listArray (1,1) [[ Attr occursMaybe "position" tns
							    ,  AnyElement occursAny AnyNS
							    ]] }
      where xc = toXMLTypeA (undefined::a)
{-    xmlDecode = do s <- get
		   DB.trace "ArrayElement:" $ return ()
		   DB.trace (show $ particles s) $ return ()
		   pos <- readAttribute occursMaybe "position" tns
                   DB.trace (show $ attributes s) $ return ()
		   DB.trace (show pos) $ return ()
                   case (particles s) of
                     (Leaf (_, a):_) -> map getChildren $ maybeNs n q $$ a

                   x <- xmlDecodeA
		   return (SOAPArrayElement (SOAPArrayIndex []) x)-}
		     

instance XMLNamespace (SOAPArrayRaw a) where
    namespaceURI _ = tns
    defaultPrefix _ = prefix


instance (Data DictXMLData (SOAPArrayRaw a), Data DictXMLData a, Data DictXMLData (SOAPArrayElement a), Data DictXMLData [SOAPArrayElement a]) => XMLData (SOAPArrayRaw a) where
    toXMLType x = xmlType { elementNames = ["Array"] 
			  , fieldSchema = listArray (1,1) [[fromMaybe (Elem occursOnce "item" Nothing) (defaultSchema xc)]] }
	where xc = toXMLTypeA (undefined::a)


--    xmlEncode dm (SOAPArrayRaw x) = [SNode $ map (xmlEncode dm) x]
    xmlDecode = do s <- get
--		   DB.trace "SOAPArray:" $ return ()
--		   DB.trace (show $ particles s) $ return ()
		   case (particles s) of
		          (SLeaf (es,_):_) -> do --DB.trace (xshow es) $ return ()
                                                 put s{particles = map (\e -> SLeaf (getChildren e, getAttrl e)) es}
						 x <- xmlDecodeA
						 -- get >>= return . DB.trace . show . particles
						 return $ SOAPArrayRaw x
			  _ -> mzero
--		     DB.trace (show $ particles s) $ xmlDecodeDefault q (undefined::(SOAPArrayRaw a))
    		      
soapArrayType = "Array"

{-

-- | A Type for holding a SOAP Array type
type ArrayTypeValue = (ArrayType, ArraySize)

data ArrayType = ArrayType{arrayType::QName, arrayRank::[UpperBound]} deriving Show
type ArraySize = [Int]

atypeValueToType :: Name -> ArrayTypeValue -> TypeQ
atypeValueToType bty atv = appT (conT ''SOAPArray) (appT (appT (conT bty) (atuple alength)) aty)
  where atuple n = let ty = conT ''Int in
		       if (n==1) then if (alength==1) then ty else appT (tupleT alength) ty
	                         else appT (atuple (n-1)) ty
        atype = fst atv
        asize = snd atv
        arank = arrayRank atype
        alength = let l = length arank in if (l==0) then 1 else l
        aty = conT $ mkName $ qnameToModule $ arrayType atype


-- FIXME : The array info deserializer is rather hacky atm.
parseArrayTypeValue :: NamespaceTable -> String -> Maybe ArrayTypeValue
parseArrayTypeValue nst s = let l = delimit s '[' in
			       if ((length l)<2) 
				  then Nothing
				  else let (t:r:s) = l in
					  do atype <- parseArrayType t r
					     asize <- mapM (readM . init) s
					     return (atype, asize)

   where parseArrayType t r = let t' = setNamespace nst $ parseQName t in 
				   do rank <- ((liftM $ (\x -> if (null x) then [Unbounded] 
							                   else map Bounded x)) (readM ("["++r) :: Maybe [Int]))
					       `mplus` (return $ replicate (length r) Unbounded)
				      return (ArrayType t' rank)

wsdlNS = "http://schemas.xmlsoap.org/wsdl/"
soapNS = "http://schemas.xmlsoap.org/wsdl/soap/"

-- | The hook for the XSD Type-mapper which recognized and deployes SOAP Arrays. Takes a Name signifying the
-- type which all SOAP Arrays should be mapped to.


arrayHook :: Name -> ComplexTypeHook
arrayHook ty nst ns t = do name <- ctype_name t
		        
                           res <- getUnion (ctype_content t) >>= getUnion . ccont_content
			
                           rc  <- if ((localPart (cres_base res), namespaceUri (cres_base res)) == ("Array", soapNS))
	    		             then Nothing
 				     else return (cres_content res)

                        

			   let alist = hHead $ hTail rc
		
                        

                           ats <- alistToAType alist

			   atype <- parseArrayTypeValue nst ats

                           return $ do x <- tySynD (mkName name) [] (atypeValueToType ty atype)
				       return [x]
                        
alistToAType :: [Union (Attribute :|: AttributeGroup :|: HNil)] -> Maybe String
alistToAType l = (liftM fromJust) $ find isJust $ map ((lookupAttrSet ("arrayType", wsdlNS) . attr_anyAttr) .?. const Nothing) l
-}
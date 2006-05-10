{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Schema.TypeMapper
-- Copyright   :  (c) Simon Foster 2005
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  aca01sdf@shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- This module will, when completed, allow mapping from XML Schema ComplexTypes to GXS
-- serializable data-types, and vice-versa. For now, it allows preliminary mapping from
-- GXS data-types to Schema and mapping from a large range of XML Schema complex-types to Haskell
-- via TH.
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

module Text.XML.Schema.TypeMapper where

import Text.XML.Schema.Utils
import Text.XML.Serializer hiding (Sequence,Choice)
import qualified Text.XML.Serializer as GXS
import Org.W3.N2001.XMLSchema
import Org.W3.N2001.XMLSchema_instance
import Control.Monad
import Data.Generics2
import Data.Union
import Text.XML.HXT.Parser hiding (mkName)
import Text.XML.HXT.Aliases
import Text.XML.HXT.IO.GetHTTPNative as HTTP
import Text.XML.HXT.IO.GetFILE as FILE
import Data.List
import Data.HList
import Data.Maybe
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Network.URI
import Data.Array
import Network.HTTP
import Data.Generics.Serializer
import Text.Regex


import Debug.Trace as DB


-- | The type of all ComplexType Hooks, a Hook is a special way of dealing with complex-types when
-- they are an extension of some kind (e.g. SOAP Arrays).
type ComplexTypeHook = NamespaceTable -> Maybe URI -> ComplexType -> Maybe (Q [Dec])

-- | A Dictionary for XSD Types.
data DictXSDType a = DictXSDType { xsdTypeD :: a -> [String] }

instance XSDType a => Sat (DictXSDType a) where
    dict = DictXSDType xsdType
    
xsdTypeA :: Data DictXSDType a => a -> [String]
xsdTypeA (x::a) = xsdTypeD (dict::DictXSDType a) x

-- | Convert a type to a ComplexType representation at run-time.
toComplexType :: (Data DictXSDType a, Data DictXMLData a) => a -> ComplexType
toComplexType t = simpleComplexType name ccont []
    where name  = head $ xsdTypeD dict t
          ccont = if (isInterleaved xcons) then error "FIXME: Interleaving not yet implemented"
		                           else setUnion $ Sequence (Just 1) (Just (Bounded 1)) (zipWith3 mapFieldSchema childNS childTypes (getConsSchema xcons))
	  xcons      = toXMLTypeA t
          childTypes = gmapQ (undefined::DictXSDType ()) (head . xsdTypeA) t
	  childNS    = map (maybe "" show) $ gmapQ (undefined::DictXMLData ()) namespaceURIA t
          thisNS     = maybe "" show $ namespaceURIA t


mapFieldSchema :: String -> String -> PartSchema -> U5 Element Group Choice Sequence Any
mapFieldSchema tns tn f = 
    case f of Elem c n ns  -> U51 $ simpleElement n (Just (QN "" tn tns)) c



moduleNameRegex    = mkRegex "@MODULE_NAME@"
schemaImportsRegex = mkRegex "@SCHEMA_IMPORTS@"
schemaUrlRegex     = mkRegex "@SCHEMA_URL@"
schemaBodyRegex    = mkRegex "@SCHEMA_BODY@"

schemaModuleTemplate = "SchemaModule.hs.in"

-- | Take a location, target namespace, list of dependencies and list of hooks and generate a module generator for the schema.
genSchemaModule :: String -> FilePath -> [ComplexTypeHook] -> IO ()
genSchemaModule i base hs = 
                       do tpt <- readFile schemaModuleTemplate
			  let u   = parseURI i
			  f <- do i' <- maybe (FILE.getCont i)
				        (\x -> HTTP.getCont i "" >>= return . either Left (Right . snd)) u
				  either error return i'
			  
                          let xml = xparse $ mkRootTree [] $ xread f
                              tns = fromJust $ parseURI $ xshow $ getChildren $ head $ (multi $ (getAttrl .> hasLocalPart "targetNamespace")) $$ xml
			      nst = getNamespaceTable (head xml)
                              ons = delete tns $ nub $ map (fromJust.parseURI.snd) nst
                              modname   = uriToModule tns
			      imports   = concat $ intersperse "\n" $ map (("import "++) . uriToModule) ons
			      path      = (concat $ intersperse "/" $  backwardURI tns) ++ ".hs"

                          createURIPath base tns
			  body <- runQ (mapFromSchema xml hs)

			  let reps      = [(moduleNameRegex, modname), (schemaImportsRegex, imports)
					  , (schemaBodyRegex, pprint body)]
			      cont      = foldr ($) tpt $ map (\(r,s) i -> subRegex r i s) reps
			  
                     

                          writeFile (base++path) cont
				    
				

-- | Take a URL or filename and a list of hooks and create a sequence of declarations for each complex-type.
mapFromSchema :: XmlTrees -> [ComplexTypeHook] -> Q [Dec]
mapFromSchema xml hs = do let nst = getNamespaceTable (head xml)
			      schema  = fromMaybe (error "Invalid Schema") $ deserializeXML xml
			      tns     = (schema_targetNamespace schema)
			      runMap  = \x -> fromJust $ (runCTHooks nst tns x hs `mplus` (return $ fromComplexType tns x))
		          (liftM concat) $ mapM runMap (schema_types schema)

runCTHooks :: NamespaceTable -> Maybe URI -> ComplexType -> [ComplexTypeHook] -> Maybe (Q [Dec])
runCTHooks nst ns ct hs = msum $ map (\f -> f nst ns ct) hs

-- | Derive an instance of XSDType
deriveXSDType :: String -> Q [Dec]
deriveXSDType name = let hname = toHaskellName name in
			 do x <- instanceD (cxt []) (appT (conT ''XSDType) (conT (mkName hname))) [funD (unqualName 'xsdType) [clause [wildP] (normalB (listE [litE (stringL name)])) []]]
			    return [x]
			 
-- | Derive an instance of XMLNamespace
deriveXMLNamespace :: Maybe URI -> String -> Q [Dec]
deriveXMLNamespace ns name = let hname = toHaskellName name in
			 do x <- instanceD (cxt []) (appT (conT ''XMLNamespace) (conT (mkName hname))) [funD (unqualName 'namespaceURI) [clause [wildP] (normalB [|ns|]) []]]
			    return [x]

-- | Map a complex type to a sequence of declarations
fromComplexType :: Maybe URI -> ComplexType -> Q [Dec]
fromComplexType ns ct = let name = fromMaybe (error "Found complexType with no name!") (ctype_name ct) in
			    (fromCompCC   name ns .?.
			     fromCompPart name ns .?.
			     error "FIXME: Unhandled complexType content") (ctype_content ct)

-- | Map complex-content to a number of declarations.
fromCompCC :: String -> Maybe URI -> ComplexContent -> Q [Dec]
fromCompCC name ns cc = dataD (cxt []) (mkName name) [] [normalC (mkName name) []] [] >>= \x -> return [x]
-- FIXME : Now GXS can do extensions, it should be possible to implement complex content fully.

-- | Map a complex particle to a number of declarations.
fromCompPart :: String -> Maybe URI -> (Union (Group  :|: All :|: Choice :|: Sequence :|: HNil) :*: 
                                       [Union (Attribute :|: AttributeGroup :|: HNil)]          :*: HNil)
					  -> Q [Dec]
fromCompPart n ns l = (fromCompSeq n ns .?.
		       fromCompInter n ns .?.
		       error "FIXME: Unhandled complexType particle content") (hHead l)

fromCompInter :: String -> Maybe URI -> All -> Q [Dec]
fromCompInter name ns all = 
    let (ts, ps) = unzip $ fromInter all
        hname    = toHaskellName name
	ps'      = map (\f -> f ns) ps 
	dec      = dataD (cxt []) (mkName hname) [] [normalC (mkName hname) (map (strictType notStrict) ts)] []
	xc       = [d| toXMLConstr _ _ = xmlConstr { fieldSchema = listArray (1,1) [ps'], isInterleaved = True, elementNames = [name] } |] >>= return . head
        ins      = instanceD (cxt [appT (appT (conT ''Data) (appT (conT ''DictXMLData) (varT (mkName "h")))) (conT (mkName hname))]) (appT (appT (conT ''XMLData) (varT (mkName "h"))) (conT (mkName hname))) [xc] in
	   do x <- dec
              i <- ins
              d <- deriveOneFromDec dec
              xns <- deriveXMLNamespace ns name
              xsi <- deriveXSDType name
	      return $ [x] ++ [i] ++ d ++ xns ++ xsi

fromCompSeq :: String -> Maybe URI -> Sequence -> Q [Dec]
fromCompSeq name ns seq = 
    let (ts, ps) = unzip $ fromSeq seq
        hname    = toHaskellName name
	ps'      = map (\f -> f ns) ps 
	dec      = dataD (cxt []) (mkName hname) [] [normalC (mkName hname) (map (strictType notStrict) ts)] []
	xc       = [d| toXMLConstr _ _ = xmlConstr { fieldSchema = listArray (1,1) [ps'] } |] >>= return . head
        ins      = instanceD (cxt [appT (appT (conT ''Data) (appT (conT ''DictXMLData) (varT (mkName "h")))) (conT (mkName hname))]) (appT (appT (conT ''XMLData) (varT (mkName "h"))) (conT (mkName hname))) [xc] in
	   do x <- dec
              i <- ins
              d <- deriveOneFromDec dec
              xns <- deriveXMLNamespace ns name
              xsi <- deriveXSDType name
	      return $ [x] ++ [i] ++ d ++ xns ++ xsi

			       
-- | Map a sequence to a TH type and unqualified part schema
fromSequence :: Sequence -> (TypeQ, Maybe URI -> PartSchema)
fromSequence x = let (ts, ps) = unzip $ fromSeq x in
		     (occursType x $ mkSeqType ts, seqN (mkOccurs x) ps)

-- | Map a choice to a TH type and unqualified part schema		     
fromChoice :: Choice -> (TypeQ, Maybe URI -> PartSchema)
fromChoice x = let (ts, ps) = unzip $ fromCho x in
		     (occursType x $ mkChoiceType ts, choiceN (mkOccurs x) ps)

-- | Make a sequence data representation from a list of types.
mkSeqType :: [TypeQ] -> TypeQ
mkSeqType [] = [t| HNil |]
mkSeqType (h:t) = appT (appT (conT ''HCons) h) (mkSeqType t)

-- | Make a choice data representation from a list of types.
mkChoiceType :: [TypeQ] -> TypeQ
mkChoiceType l = appT (conT ''Union) (mkSeqType l)

fromSeq :: Sequence -> [(TypeQ, Maybe URI -> PartSchema)]
fromSeq = map fromParticle . seq_content

fromCho :: Choice -> [(TypeQ, Maybe URI -> PartSchema)]
fromCho = map fromParticle . cho_content

fromInter :: All -> [(TypeQ, Maybe URI -> PartSchema)]
fromInter = map fromElement . all_content

-- | Map an XSD particle to a type and unqualified part schema
fromParticle :: Union (Element :|: Group :|: Choice :|: Sequence :|: Any :|: HNil) -> (TypeQ, Maybe URI -> PartSchema)
fromParticle = fromElement  .?.
	       fromSequence .?.
	       fromChoice   .?.
	       -- FIXME : I think all can only occur at top-level, so we don't need it here. Check this is correct.
	       -- FIXME : We need parametric types to map wildcards, too much work for now...
               error "FIXME: fromParticle: Unhandled particle type!"

-- | Map an element to a type and unqualified part schema
fromElement :: Element -> (TypeQ, Maybe URI -> PartSchema)
fromElement e = let ty = fromMaybe (error "FIXME: fromElement can only handle elements with type attributes") (element_type e) in
			 (occursType e $ conT (mkName $ qnameToModule ty), elmN (mkOccurs e) (element_name e))

-- | Give a type cardinality representation, e.g. if it occurs many times, put the type in a list.
occursType :: Cardinality a => a -> TypeQ -> TypeQ
occursType o t = case (minOccurs o, maxOccurs o) of
		     (1, Bounded 1) -> t
		     (0, Bounded 1) -> appT (conT ''Maybe) t
		     _              -> appT listT t		     



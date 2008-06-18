{-# OPTIONS -fth -cpp #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.HXT.Aliases
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A set of utils and aliases for HXT.
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
module Text.XML.HXT.Aliases
    ( module Text.XML.HXT.Aliases
    , module Text.XML.HXT.DOM.QualifiedName
    ) where

import Text.XML.HXT.Parser
import Text.XML.HXT.DOM.QualifiedName
import Network.HTTP
import Network.URI
import Data.Char
import Data.List
import Data.Maybe
import qualified Control.Exception as CE
import Language.Haskell.TH.Syntax

-- | Shorthand, got fed up of typing hasLocalPart over and over.
hasLP :: String -> XmlFilter
hasLP = hasLocalPart

-- | Parse the XML file given by the String, does not do DTD validation as it doesn't seem to work when trying to parse XML Schema Schema.
parseXML :: String -> IO (Maybe XmlTrees)
parseXML t = do

    let x =
            ({-setSystemParams
            .>>
            parseXmlDoc
            .>>
            liftMf transfAllCharRef        -}
            checkWellformedDoc
            .>>
            liftF canonicalizeAllNodes -- Remove Header and bits we aren't interested in
            .>>
            liftF propagateNamespaces  -- Propogate namespace URIs down the tree
            .>>
            liftF (removeDocWhiteSpace)
            .>>
            liftF (getChildren)
            ) (head $ tag "/" []  [mkXText t] emptyRoot)

    t <- run' x
    return $ if (null t) then Nothing else Just t

-- | Print an XML Tree to stdout
putXML :: XmlTrees -> IO ()
putXML = putStrLn . xmlTreesToString

-- | Given a URI, return a parse XmlTrees
getXML :: URI -> IO (Maybe XmlTrees)
getXML u = do h <- CE.catch (simpleHTTP (Request u GET [] "")) (\x -> return $ Left undefined)
              case h of
                  Left _  -> return Nothing
                  Right x -> parseXML (rspBody x)



-- | Empty QName
nullQN :: QName
nullQN =  QN "" "" ""

-- | If the the two QNames have the same local parts and namespace URI they are equivelant
-- although not equal.
equalQN :: QName -> QName -> Bool
equalQN q1 q2 = (localPart q1) `equalURL` (localPart q2) && (namespaceUri q1) `equalURL` (namespaceUri q2)

-- | Tests two urls as Strings for equality, strip slashes and normalize
equalURL :: String -> String -> Bool
equalURL s1 s2 = ((map toLower $ stripSlash s1) == (map toLower $ stripSlash s2))

-- | Remove a trailing slash from a string if one exists.
stripSlash :: String -> String
stripSlash "" = ""
stripSlash s
    | (last s == '/') = init s
    | otherwise = s

-- | Tries it's best to resolve\/fully qualify a QName by filling in missing fields, if possible. Will
-- also correct the prefix if incorrect.
resolveQName :: NamespaceTable -> QName -> QName
resolveQName _ q@(QN "" l "") = q
resolveQName nt (QN "" l u) = let p = fromMaybe "" $ lookup u (map (\(x,y)->(y,x)) nt) in QN p l u
resolveQName nt (QN p l "") = let u = fromMaybe "" $ lookup p nt in QN p l u
resolveQName nt (QN _ l u) = resolveQName nt (QN "" l u)

-- | Get the namespace prefix\/uri mapping table from a given XML Tree.
getNamespaceTable :: XmlTree -> NamespaceTable
getNamespaceTable t = map (\x -> ((localPartOf x),(xmlTreesToString (getChildren x)))) (getNSTableAux t)
getNSTableAux t = topNS ++ otherNS
    where
    topNS = ((getAttrl .> isOfAttr ((\(px, lp) -> (px == "xmlns" && lp /= ":")) . span (/= ':') . aName)) t)
    otherNS = (concat (map getNSTableAux (getChildren t)))

getAllNamespaces :: XmlTree -> [String]
getAllNamespaces (NTree t s) = (case t of
                                       XTag  (QN _ _ ns) as -> ns : (concat $ map getAllNamespaces as)
                                       XPi   (QN _ _ ns) as -> ns : (concat $ map getAllNamespaces as)
                                       XAttr (QN _ _ ns)    -> [ns]
                                       _                    -> []
                               ) ++ (concat $ map getAllNamespaces s)


-- | Generated a new namespacetable for an XML Tree
generateNamespaceTable :: XmlTrees -> NamespaceTable
generateNamespaceTable ts = zipWith (\ns n -> ("tns"++show n, ns)) (nub $ filter (not.null) $ concat $ map getAllNamespaces ts) [0..]

-- | Top-down replacement of all element and attribute namespace prefixes.
applyNamespaceTable :: NamespaceTable -> XmlFilter
applyNamespaceTable nst = (processTopDown $ (modifyQName (resolveQName nst) .> processAttr (modifyQName (resolveQName nst))) `when` isXTag)

{-
-- FIXME: Why does modifyQName in HXT not echo content without a QName, deleting it instead?
modifyQName'                            ::  (TagName -> TagName) -> XmlFilter
modifyQName' f (NTree (XTag n al) cs)   = [NTree (XTag (f n) al) cs]
modifyQName' f (NTree (XPi  n al) cs)   = [NTree (XPi  (f n) al) cs]
modifyQName' f (NTree (XAttr n)   cs)   = [NTree (XAttr (f n)  ) cs]
modifyQName' _ x                        = [x]
-}

declareNamespaces :: NamespaceTable -> XmlFilter
declareNamespaces = cat . map (\(p, ns)->attr ("xmlns:"++p) (txt ns))
parseQName :: String -> QName
parseQName x =  let sp = span (/= ':') x in
                     if (null $ snd sp) then (QN "" (fst sp) "")
                                        else (QN (fst sp) (tail $ snd sp) "")


parseUName :: String -> QName
parseUName x =  let sp = span (/= '}') x in
                     if (null $ snd sp) then (QN "" (fst sp) "")
                                        else (QN "" (tail $ snd sp) (tail $ fst sp))

-- | Remove all namespace prefix declarations from a tree
removeNamespaceDecs :: XmlFilter
removeNamespaceDecs = (processTopDown $ processAttr (none `when` hasPrefix "xmlns"))

qnameOf :: XmlTree -> QName
qnameOf t = (QN (prefixOf t) (localPartOf t) (namespaceOf t))

hasAttrValue            :: String -> (String -> Bool) -> XmlFilter
hasAttrValue a p t
   | (not . null) att
     &&
     p val
       = [t]
   | otherwise
       = []
   where
   att = getAttrl .> isAttr a $ t
   val = xshow . getChildren $$ att

hasNsAttrValue          :: String -> String -> (String -> Bool) -> XmlFilter
hasNsAttrValue a ns p t
   | (not . null) att
     &&
     p val
       = [t]
   | otherwise
       = []
   where
   att = getAttrl .> hasLocalPart a .> hasNamespace ns $ t
   val = xshow . getChildren $$ att


insertAttrl                             :: XmlTrees -> XmlFilter
insertAttrl al (NTree (XTag n _al) cs) = [ NTree (XTag n (_al++al)) cs ]
insertAttrl al (NTree (XPi  n _al) cs) = [ NTree (XPi  n (_al++al)) cs ]
insertAttrl _ _                        = []


modifyNsAttr                            :: String -> String -> (String -> String) -> XmlFilter
modifyNsAttr an ns f
    = processAttr (modifyValue `when` isNsAttr an ns)
      where
      modifyValue = modifyChildren ((modifyText f $$) . xmlTreesToText)


-- FIXME : This should be done properly via lazy IO.
resolveHREFs :: XmlFilter
resolveHREFs t = resolveHREFsRoot t t
  where
  resolveHREFsRoot :: XmlTree -> XmlFilter
  resolveHREFsRoot t = (processTopDown (iff (hasAttr "href") (resolveHREF t) this))

  resolveHREF :: XmlTree -> XmlFilter
  resolveHREF rt t = let ref  = xshow $ (getAttrl .> hasLocalPart "href" .> getChildren) t
                         href = case ref of
                                ('#':h) -> h
                                x       -> x
                         cont = (multi $ hasAttrValue "id" ((==) href)) rt
                         elms = (getChildren .> resolveHREFsRoot rt) $$ cont
                         attr = getAttrl $$ cont in
                                (replaceChildren elms .> insertAttrl attr .> del1Attr "href" .> del1Attr "id") t

xmlParse s = xparse $ mkRootTree [] $ xread s

-- | Perform full canonicalization of an XML Tree.
xparse = transfAllCharRef     .>
         canonicalizeAllNodes .>
         propagateNamespaces  .>
         removeDocWhiteSpace  .>
         getChildren

resolveBaseURIs :: [(String, String)] -> String -> XmlFilter
resolveBaseURIs as u t = let b  = xshow $ getNsValue "base" xmlNamespace t
                             u' | (null b) = u
                                | (isRelativeReference b) = maybe "" show (do r1 <- parseURIReference b
                                                                              r2 <- parseURIReference u
                                                                              r1 `nonStrictRelativeTo` r2)
                                | otherwise = b
                             f = seqF $ map (\(l,ns) -> modifyNsAttr l ns (u ++)) as
                                 in processChildren (resolveBaseURIs as u' .> f) t

getXMLFragment :: String -> String -> XmlStateFilter state
getXMLFragment lp ns = getFragment
  where
       getFragment t = (getWellformedDoc .>> liftF xparse .>> liftF p) t'
        where uri = fromMaybe nullURI $ parseURI $ xshow $ getValue "source" t
              p = fromMaybe this (return $ if (null $ uriFragment uri)
                then this
                else (multi $ hasNsAttrValue lp ns ((==) (uriFragment uri))))
              t' = head $ modifyAttr "source" (const $ show uri{uriFragment=""}) t

modifyOfAttr                            :: (AttrName -> Bool) -> (String -> String) -> XmlFilter
modifyOfAttr p f
    = processAttr (modifyValue `when` isOfAttr p)
      where
      modifyValue = modifyChildren ((modifyText f $$) . xmlTreesToText)


-- Instances of Lift for HXT XML Tree data-types
#ifndef __HADDOCK__
instance Lift a => Lift (NTree a) where
    lift (NTree n ts) = [| NTree n ts |]

instance Lift QName where
    lift (QN p l n) = [| QN p l n |]

instance Lift XNode where
    lift (XText s)      = [| XText s |]
    lift (XCharRef i)   = [| XCharRef i |]
    lift (XEntityRef s) = [| XEntityRef s |]
    lift (XCmt s)       = [| XCmt s |]
    lift (XCdata s)     = [| XCdata s |]
    lift (XPi q ts)     = [| XPi q ts |]
    lift (XTag q ts)    = [| XTag q ts |]
    lift (XDTD d as)    = [| XDTD d as |]
    lift (XAttr q)      = [| XAttr q |]
    lift (XError i s)   = [| XError i s |]

instance Lift DTDElem where
    lift DOCTYPE  = [| DOCTYPE  |]
    lift ELEMENT  = [| ELEMENT  |]
    lift CONTENT  = [| CONTENT  |]
    lift ATTLIST  = [| ATTLIST  |]
    lift ENTITY   = [| ENTITY   |]
    lift PENTITY  = [| PENTITY  |]
    lift NOTATION = [| NOTATION |]
    lift CONDSECT = [| CONDSECT |]
    lift NAME     = [| NAME     |]
    lift PEREF    = [| PEREF    |]
#endif

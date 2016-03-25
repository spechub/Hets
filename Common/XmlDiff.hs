{- |
Module      :  ./Common/XmlDiff.hs
Description :  compute xml diffs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Common.XmlDiff where

import Common.ToXml
import Common.Utils as Utils
import Common.XPath
import Common.XUpdate

import Common.Lib.MapSet (setToMap)

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light as XML

hetsTags :: UnordTags
hetsTags = Map.fromList
  $ map (\ (e, as) -> (unqual e, Set.fromList $ map unqual as))
  [ ("DGNode", ["name"])
  , ("DGLink", ["linkid", "source", "target"])
  , ("Axiom", [])
  , ("Theorem", []) ]
{- for symbols the order matters. For axioms and theorems the names should be
stored separately -}

hetsXmlChanges :: Element -> Element -> [Change]
hetsXmlChanges e1 e2 = xmlDiff hetsTags [] Map.empty
  [Elem $ cleanUpElem e1]
  [Elem $ cleanUpElem e2]

hetsXmlDiff :: Element -> Element -> Element
hetsXmlDiff e = mkMods . hetsXmlChanges e

{- for elements, whose order does not matter, use the given attribute keys to
determine their equality. An empty set indicates an element that only contains
text to be compared. -}
type UnordTags = Map.Map QName (Set.Set QName)

-- keep track of the nth element with a given tag
type Count = Map.Map QName Int

{- we assume an element contains other elements and no text entries or just a
single text content -}

xmlDiff :: UnordTags -> [Step] -> Count -> [Content] -> [Content] -> [Change]
xmlDiff m stps em old new = case (old, filter validContent new) of
  ([], []) -> []
  ([], ns) ->
    [Change (Add Append $ map contentToAddChange ns) $ pathToExpr stps]
  (os, []) -> removeIns stps em os
  (o : os, ns@(n : rt)) ->
    if validContent o then
    case o of
      Elem e ->
        let en = elName e
            atts = elAttribs e
            cs = elContent e
            (nm, nstps) = extendPath en em stps
            downDiffs = xmlElemDiff m nstps atts cs
            restDiffs = xmlDiff m stps nm os
            rmO = Change Remove (pathToExpr nstps) : restDiffs ns
        in case Map.lookup en m of
        Nothing -> case n of
          Elem e2 | elName e2 == en ->
             downDiffs e2
             ++ restDiffs rt
          _ -> rmO
        Just ats -> let
            (mns, rns) = partition (matchElems en (strContent e) $
              Map.intersection (attrMap atts) $ setToMap ats) ns
            in case mns of
            Elem mn : rm -> downDiffs mn
              ++ restDiffs (rm ++ rns)
            _ -> rmO
      XML.Text cd -> let inText = cdData cd in case n of
        XML.Text cd2 | trim inText == trim nText
            -> xmlDiff m stps em os rt
          | otherwise -> Change (Update nText) (pathToExpr stps)
              : xmlDiff m stps em os rt
          where nText = cdData cd2
        _ -> error "xmldiff2"
      _ -> error "xmldiff"
    else xmlDiff m stps em os ns

removeIns :: [Step] -> Count -> [Content] -> [Change]
removeIns stps em cs = case cs of
  [] -> []
  c : rs -> case c of
    Elem e -> let
      (nm, nstps) = extendPath (elName e) em stps
      in Change Remove (pathToExpr nstps) : removeIns stps nm rs
    _ -> Change (Update "") (pathToExpr stps) : removeIns stps em rs
         -- does not work for multiple text entries

attrMap :: [Attr] -> Map.Map QName String
attrMap = Map.fromList . map (\ a -> (attrKey a, attrVal a))

matchElems :: QName -> String -> Map.Map QName String -> Content -> Bool
matchElems en t atts c = case c of
  Elem e -> elName e == en
    && if Map.null atts then null (elChildren e) && strContent e == t else
           Map.isSubmapOfBy (==) atts (attrMap $ elAttribs e)
  _ -> False

xmlElemDiff :: UnordTags -> [Step] -> [Attr] -> [Content] -> Element -> [Change]
xmlElemDiff m nPath atts cs e2 = xmlAttrDiff nPath atts (elAttribs e2)
  ++ xmlDiff m nPath Map.empty cs (elContent e2)

xmlAttrDiff :: [Step] -> [Attr] -> [Attr] -> [Change]
xmlAttrDiff p a1 a2 = let
  m1 = attrMap a1
  m2 = attrMap a2
  rms = Map.toList $ Map.difference m1 m2
  ins = Map.toList $ Map.difference m2 m1
  inter = Map.toList $ Map.filter (uncurry (/=))
    $ Map.intersectionWith (,) m1 m2
  addAttrStep a = pathToExpr $ Step Attribute (NameTest $ qName a) [] : p
  in map (Change Remove . addAttrStep . fst) rms
     ++ map (\ (a, (_, v)) -> Change (Update v) $ addAttrStep a) inter
     ++ if null ins then [] else
       [Change (Add Append $ map (AddAttr . uncurry Attr) ins) $ pathToExpr p]

pathToExpr :: [Step] -> Expr
pathToExpr = PathExpr Nothing . Path True . reverse

extendPath :: QName -> Count -> [Step] -> (Count, [Step])
extendPath en em stps = let
  nm = Map.insertWith (+) en 1 em
  i = Map.findWithDefault 1 en nm
  nstps = Step Child (NameTest $ qName en) [PrimExpr Number $ show i] : stps
  in (nm, nstps)

-- steps and predicates are reversed!
addPathNumber :: Int -> [Step] -> [Step]
addPathNumber i stps =
  let e = PrimExpr Number $ show i
  in case stps of
  [] -> []
  Step a n es : rs -> Step a n (e : es) : rs

contentToAddChange :: Content -> AddChange
contentToAddChange c = case c of
  Elem e -> AddElem e
  XML.Text t -> AddText $ cdData t
  CRef s -> AddText s

mkXQName :: String -> QName
mkXQName s = (unqual s) { qPrefix = Just xupdateS }

changeToXml :: Change -> Element
changeToXml (Change csel pth) = let
  sel = add_attr (mkAttr selectS $ show pth)
  in case csel of
  Add i as -> sel
    . node (mkXQName $ showInsert i) $ map addsToXml as
  Remove -> sel $ node (mkXQName removeS) ()
  Update s -> sel $ node (mkXQName updateS) s
  _ -> error "changeToXml"

addsToXml :: AddChange -> Content
addsToXml a = case a of
  AddElem e -> Elem $ cleanUpElem e
  AddAttr (Attr k v) -> Elem
    . add_attr (mkNameAttr $ qName k) $ node (mkXQName attributeS) v
  AddText s -> mkText s
  _ -> error "addsToXml"

mkMods :: [Change] -> Element
mkMods = node (mkXQName "modifications") . map changeToXml

{- |
Module      :  $Header$
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

import Data.Char
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light as XML

{- for elements, whose order does not matter, use the given attribute keys to
determine their equality. -}
type UnordTags = Map.Map QName (Set.Set QName)

xmlDiff :: UnordTags -> [Step] -> Int -> [Content] -> [Content] -> [Change]
xmlDiff m pth i old new = let
  np = addPathNumber (i + 1) pth
  pe = pathToExpr np
  in case (old, filter validContent new) of
  ([], []) -> []
  ([], ns) ->
    [Change (Add Append $ map contentToAddChange ns) pe]
  (os, []) -> map
    (\ (_, j) -> Change Remove $ pathToExpr $ addPathNumber (i + j) pth)
    $ Utils.number os
  (o : os, ns@(n : rt)) -> let
    restDiffs = xmlDiff m pth (i + 1) os
    rmO = Change Remove pe : restDiffs ns
    in if validContent o then
    case o of
      Elem e ->
        let en = elName e
            atts = elAttribs e
            cs = elContent e
            nPath = extendPath en np
        in case Map.lookup en m of
        Nothing -> case n of
          Elem e2 | elName e2 == en ->
             xmlElemDiff m nPath atts cs e2
             ++ restDiffs rt
          _ -> rmO
        Just ats -> let
            (mns, rns) = partition (matchElems en $
              Map.intersection (attrMap atts) $ setToMap ats) ns
            in case mns of
            Elem mn : rm -> xmlElemDiff m nPath atts cs mn
              ++ restDiffs (rm ++ rns)
            _ -> rmO
      XML.Text cd -> case n of
        XML.Text cd2 | trim (cdData cd) == trim nText
            -> restDiffs rt
          | otherwise -> Change (Update nText) pe : restDiffs rt
          where nText = cdData cd2
        _ -> rmO
      _ -> rmO
    else restDiffs ns

attrMap :: [Attr] -> Map.Map QName String
attrMap = Map.fromList . map (\ a -> (attrKey a, attrVal a))

matchElems :: QName -> Map.Map QName String -> Content -> Bool
matchElems en atts c = case c of
  Elem e | elName e == en
    && Map.isSubmapOfBy (==) atts (attrMap $ elAttribs e) -> True
  _ -> False

xmlElemDiff :: UnordTags -> [Step] -> [Attr] -> [Content] -> Element -> [Change]
xmlElemDiff m nPath atts cs e2 = xmlAttrDiff nPath atts (elAttribs e2)
  ++ xmlDiff m nPath 0 cs (elContent e2)

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

extendPath :: QName -> [Step] -> [Step]
extendPath q = (Step Child (NameTest $ qName q) [] :)

-- steps and predicates are reversed!
addPathNumber :: Int -> [Step] -> [Step]
addPathNumber i stps =
  let e = PrimExpr Number $ show i
  in case stps of
  [] -> []
  Step a n es : rs -> Step a n (e : es) : rs

validContent :: Content -> Bool
validContent c = case c of
  XML.Text t | all isSpace $ cdData t -> False
  CRef _ -> False -- we cannot handle this
  _ -> True

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
  Add _ as -> sel
    . node (mkXQName appendS) $ map addsToXml as
  Remove -> sel $ node (mkXQName removeS) ()
  Update s -> sel $ node (mkXQName updateS) s
  _ -> error "changeToXml"

addsToXml :: AddChange -> Content
addsToXml a = case a of
  AddElem e -> Elem e
  AddAttr (Attr k v) -> Elem
    . add_attr (mkNameAttr $ qName k) $ node (mkXQName attributeS) v
  AddText s -> mkText s
  _ -> error "addsToXml"

mkMods :: [Change] -> Element
mkMods = node (mkXQName "modifications") . map changeToXml

module Common.XmlDiff where

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

xmlDiff :: UnordTags -> Path -> Int -> [Content] -> [Content] -> [Change]
xmlDiff m pth i old new = case (old, filter validContent new) of
  ([], []) -> []
  ([], ns) ->
    [Change (Add Append $ map contentToAddChange ns) $ pathToExpr pth]
  (os, []) -> map
    (\ (_, j) -> Change Remove $ pathToExpr $ addPathNumber (i + j) pth)
    $ Utils.number os
  (o : os, ns@(n : rt)) -> let
    restDiffs = xmlDiff m pth (i + 1) os
    rmO = Change Remove (pathToExpr $ addPathNumber (i + 1) pth) : restDiffs ns
    in if validContent o then
    case o of
      Elem e ->
        let en = elName e
            atts = elAttribs e
            cs = elContent e
            nPath = extendPath en pth
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
        XML.Text cd2 | trim (cdData cd) == trim (cdData cd2)
          -> restDiffs rt
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

xmlElemDiff :: UnordTags -> Path -> [Attr] -> [Content] -> Element -> [Change]
xmlElemDiff m nPath atts cs e2 = xmlAttrDiff nPath atts (elAttribs e2)
  ++ xmlDiff m nPath 0 cs (elContent e2)

xmlAttrDiff :: Path -> [Attr] -> [Attr] -> [Change]
xmlAttrDiff _ _ _ = []

pathToExpr :: Path -> Expr
pathToExpr = PathExpr Nothing

extendPath :: QName -> Path -> Path
extendPath q (Path b stps) =
  Path b $ Step Child (NameTest $ qName q) [] : stps

-- steps and predicates are reversed!
addPathNumber :: Int -> Path -> Path
addPathNumber i (Path b stps) =
  let e = PrimExpr Number $ show i
  in Path b $ case stps of
  [] -> [Step Self Node [e]]
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

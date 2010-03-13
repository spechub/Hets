{- |
Module      :  $Header$
Description:   functions useful for all prover connections in Hets
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Functions useful for all prover connections in Hets

Some were moved from Isabelle.Translate and some others from
Isabelle.IsaProve.
-}

module Common.ProofUtils where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Utils (number)

{-
 * generic names are added

 * disambiguation of duplicate assigned names

is done by toThSens

 * translation of special characters with the aid of the provided function

is done by prepareSenNames

Warning: all sentence names are disambiguated by adding a natural number.
If that does not work for a certain reasoner you can hand in a function
which uses a different alghorithm.
-}

-- | translate special characters in sentence names
prepareSenNames :: (String -> String) -> [Named a] -> [Named a]
prepareSenNames = map . reName

-- | disambiguate sentence names
disambiguateSens :: Set.Set String -> [Named a] -> [Named a]
disambiguateSens =
    genericDisambigSens 0 senAttr $ reName . const

-- | generically disambiguate lists with names
genericDisambigSens :: Int -> (a -> String) -> (String -> a -> a)
                    -> Set.Set String -> [a] -> [a]
genericDisambigSens _ _ _ _ [] = []
genericDisambigSens c sel upd nameSet (ax : rest) =
  let name = sel ax in case Set.splitMember name nameSet of
  (_, False, _) ->
      ax : genericDisambigSens c sel upd (Set.insert name nameSet) rest
  (_, _, greater) -> let
      n = until (not . flip Set.member greater . (name ++) . ('_' :) . show)
              (+ 1) (c + 1)
      name' = name ++ '_' : show n
      in upd name' ax :
         genericDisambigSens n sel upd (Set.insert name' nameSet) rest

nameAndDisambiguate :: [Named a] -> [Named a]
nameAndDisambiguate = disambiguateSens Set.empty . nameSens

-- | name unlabeled axioms with "Axnnn"
nameSens :: [Named a] -> [Named a]
nameSens =
  map (\ (sen, no) ->
       if senAttr sen == "" then reName (const $ "Ax" ++ show no) sen else sen)
    . number

-- | collect the mapping of new to old names
collectNameMapping :: [Named a] -> [Named a] -> Map.Map String String
collectNameMapping ns os = if any (null . senAttr) os
  then error "Common.ProofUtils.collectNameMapping"
  else Map.fromList $ zipWith (\ n o -> (senAttr n, senAttr o)) ns os

-- | a separate Map speeds up lookup
charMap :: Map.Map Char String
charMap = Map.fromList
 [(' ' , "Space"),
  ('\n', "Newline"),
  ('\t', "Tab"),
  ('!' , "Exclam"),
  ('"' , "Quot"),
  ('#' , "Hash"),
  ('$' , "Dollar"),
  ('%' , "Percent"),
  ('&' , "Amp"),
  ('\'', "Prime"), -- Apostrophe?
  ('(' , "OBr"),
  (')' , "CBr"),
  ('*' , "x"),
  ('+' , "Plus"),
  (',' , "Comma"),
  ('-' , "Minus"),
  ('.' , "Period"), -- Dot?
  ('/' , "Slash"), -- Div?
  (':' , "Colon"),
  (';' , "Semi"),
  ('<' , "Lt"),
  ('=' , "Eq"),
  ('>' , "Gt"),
  ('?' , "Quest"),
  ('@' , "At"),
  ('[' , "OSqBr"),
  ('\\' , "Bslash"),
  (']' , "CSqBr"),
  ('^' , "Caret"), -- Hat?
  ('`' , "Grave"),
  ('{' , "LBrace"),
  ('|' , "VBar"),
  ('}' , "RBrace"),
  ('~' , "Tilde"),
  ('\160', "nbsp"),
  ('\161', "iexcl"),
  ('\162', "cent"),
  ('\163', "pound"),
  ('\164', "curren"),
  ('\165', "yen"),
  ('\166', "brvbar"),
  ('\167', "sect"),
  ('\168', "uml"),
  ('\169', "copy"),
  ('\170', "ordf"),
  ('\171', "laquo"),
  ('\172', "not"),
  ('\173', "shy"),
  ('\174', "reg"),
  ('\175', "macr"),
  ('\176', "deg"),
  ('\177', "plusmn"),
  ('\178', "sup2"),
  ('\179', "sup3"),
  ('\180', "acute"),
  ('\181', "micro"),
  ('\182', "para"),
  ('\183', "middot"),
  ('\184', "cedil"),
  ('\185', "sup1"),
  ('\186', "ordm"),
  ('\187', "raquo"),
  ('\188', "quarter"),
  ('\189', "half"),
  ('\190', "frac34"),
  ('\191', "iquest"),
  ('\192', "Agrave"),
  ('\193', "Aacute"),
  ('\194', "Acirc"),
  ('\195', "Atilde"),
  ('\196', "Auml"),
  ('\197', "Aring"),
  ('\198', "AElig"),
  ('\199', "Ccedil"),
  ('\200', "Egrave"),
  ('\201', "Eacute"),
  ('\202', "Ecirc"),
  ('\203', "Euml"),
  ('\204', "Igrave"),
  ('\205', "Iacute"),
  ('\206', "Icirc"),
  ('\207', "Iuml"),
  ('\208', "ETH"),
  ('\209', "Ntilde"),
  ('\210', "Ograve"),
  ('\211', "Oacute"),
  ('\212', "Ocirc"),
  ('\213', "Otilde"),
  ('\214', "Ouml"),
  ('\215', "Times"),
  ('\216', "OSlash"),
  ('\217', "Ugrave"),
  ('\218', "Uacute"),
  ('\219', "Ucirc"),
  ('\220', "Uuml"),
  ('\221', "Yacute"),
  ('\222', "THORN"),
  ('\223', "szlig"),
  ('\224', "agrave"),
  ('\225', "aacute"),
  ('\226', "acirc"),
  ('\227', "atilde"),
  ('\228', "auml"),
  ('\229', "aring"),
  ('\230', "aelig"),
  ('\231', "ccedil"),
  ('\232', "egrave"),
  ('\233', "eacute"),
  ('\234', "ecirc"),
  ('\235', "euml"),
  ('\236', "igrave"),
  ('\237', "iacute"),
  ('\238', "icirc"),
  ('\239', "iuml"),
  ('\240', "eth"),
  ('\241', "ntilde"),
  ('\242', "ograve"),
  ('\243', "oacute"),
  ('\244', "ocirc"),
  ('\245', "otilde"),
  ('\246', "ouml"),
  ('\247', "Divide"),
  ('\248', "oslash"),
  ('\249', "ugrave"),
  ('\250', "uacute"),
  ('\251', "ucirc"),
  ('\252', "uuml"),
  ('\253', "yacute"),
  ('\254', "thorn"),
  ('\255', "yuml")]

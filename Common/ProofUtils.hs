{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  lüttich@tzi.de
Stability   :  provisional
Portability :  portable

this module collects functions useful for all prover connections in Hets.
Some were moved from Isabelle.Translate and some others from
Isabelle.IsaProve.
-}

module Common.ProofUtils where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.AS_Annotation

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
    genericDisambigSens senName ( \ n s -> s { senName = n })

-- | generically disambiguate lists with names
genericDisambigSens :: (a -> String) -> (String -> a -> a) -> Set.Set String
                    -> [a] -> [a]
genericDisambigSens _ _ _ [] = []
genericDisambigSens sel upd nameSet (ax : rest) =
  let name = sel ax in case Set.splitMember name nameSet of
  (_, False, _) ->
      ax : genericDisambigSens sel upd (Set.insert name nameSet) rest
  (_, _, greater) -> let
      name' = head $ filter (not . flip Set.member greater)
                          [name++show (i :: Int) | i<-[1..]]
      in upd name' ax :
         genericDisambigSens sel upd (Set.insert name' nameSet) rest

-- | name unlabeled axioms with "Axnnn"
nameSens :: [Named a] -> [Named a]
nameSens sens =
  map nameSen (zip sens [1..length sens])
  where nameSen (sen,no) = if senName sen == ""
                              then sen{senName = "Ax"++show no}
                              else sen

-- | collect the mapping of new to old names
collectNameMapping ::Show a => [Named a] -> [Named a] -> Map.Map String String
collectNameMapping n o = Map.fromList (zipWith toPair n o)
    where toPair nSen oSen = (senName nSen,
                              if null oName
                                 then error ("Common.ProofUtils."++
                                             "collectNameMapping: sentence "++
                                             "without name found: "++
                                             show (sentence oSen))
                                 else oName)
              where oName = senName oSen

-- | a separate Map speeds up lookup
charMap :: Map.Map Char String
charMap = Map.fromList
 [('!' , "Exclam"),
  ('"' , "Quot"),
  ('#' , "Hash"),
  ('$' , "Dollar"),
  ('%' , "Percent"),
  ('&' , "Amp"),
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
  ('¡' , "iexcl"),
  ('¢' , "cent"),
  ('£' , "pound"),
  ('¤' , "curren"),
  ('¥' , "yen"),
  ('¦' , "brvbar"),
  ('§' , "sect"),
  ('¨' , "uml"),
  ('©' , "copy"),
  ('ª' , "ordf"),
  ('«' , "laquo"),
  ('¬' , "not"),
  ('­' , "shy"),
  ('®' , "reg"),
  ('\175', "macr"),
  ('°' , "deg"),
  ('±' , "plusmn"),
  ('²' , "sup2"),
  ('³' , "sup3"),
  ('´' , "acute"),
  ('µ' , "micro"),
  ('¶' , "para"),
  ('·' , "middot"),
  ('¸' , "cedil"),
  ('¹' , "sup1"),
  ('º' , "ordm"),
  ('»' , "raquo"),
  ('¼' , "quarter"),
  ('½' , "half"),
  ('¾' , "frac34"),
  ('¿' , "iquest"),
  ('À' , "Agrave"),
  ('Á' , "Aacute"),
  ('Â' , "Acirc"),
  ('Ã' , "Atilde"),
  ('Ä' , "Auml"),
  ('Å' , "Aring"),
  ('Æ' , "AElig"),
  ('Ç' , "Ccedil"),
  ('È' , "Egrave"),
  ('É' , "Eacute"),
  ('Ê' , "Ecirc"),
  ('Ë' , "Euml"),
  ('Ì' , "Igrave"),
  ('Í' , "Iacute"),
  ('Î' , "Icirc"),
  ('Ï' , "Iuml"),
  ('Ð' , "ETH"),
  ('Ñ' , "Ntilde"),
  ('Ò' , "Ograve"),
  ('Ó' , "Oacute"),
  ('Ô' , "Ocirc"),
  ('Õ' , "Otilde"),
  ('Ö' , "Ouml"),
  ('×' , "Times"),
  ('Ø' , "OSlash"),
  ('Ù' , "Ugrave"),
  ('Ú' , "Uacute"),
  ('Û' , "Ucirc"),
  ('Ü' , "Uuml"),
  ('Ý' , "Yacute"),
  ('Þ' , "THORN"),
  ('ß' , "szlig"),
  ('à' , "agrave"),
  ('á' , "aacute"),
  ('â' , "acirc"),
  ('ã' , "atilde"),
  ('ä' , "auml"),
  ('å' , "aring"),
  ('æ' , "aelig"),
  ('ç' , "ccedil"),
  ('è' , "egrave"),
  ('é' , "eacute"),
  ('ê' , "ecirc"),
  ('ë' , "euml"),
  ('ì' , "igrave"),
  ('í' , "iacute"),
  ('î' , "icirc"),
  ('ï' , "iuml"),
  ('ð' , "eth"),
  ('ñ' , "ntilde"),
  ('ò' , "ograve"),
  ('ó' , "oacute"),
  ('ô' , "ocirc"),
  ('õ' , "otilde"),
  ('ö' , "ouml"),
  ('÷' , "Divide"),
  ('ø' , "oslash"),
  ('ù' , "ugrave"),
  ('ú' , "uacute"),
  ('û' , "ucirc"),
  ('ü' , "uuml"),
  ('ý' , "yacute"),
  ('þ' , "thorn"),
  ('ÿ' , "yuml")]

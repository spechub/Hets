{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   translate 'Id' to Isabelle strings
-}

module Isabelle.Translate (showIsaT, showIsaIT, replaceChar, transString) where

import Common.Id 
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Data.Char
import Isabelle.IsaSign
import Isabelle.IsaStrings

------------------- Id translation functions -------------------
isaPrelude :: Map.Map BaseSig (Set.Set String)
isaPrelude = Map.fromList 
  [(MainHC_thy, foldr Set.insert mainS ["pApp","apt","app","defOp","pair"]),
   (Main_thy, mainS), (HOLCF_thy, holcfS), 
   (HOL_thy, holS), (Pure_thy, pureS)]

showIsaT :: Id -> BaseSig -> String 
showIsaT ident theory = let sident = transString $ show ident in
  if Set.member sident $ Map.findWithDefault Set.empty theory isaPrelude 
  then sident++"X" else sident

showIsaIT :: Id -> Int -> BaseSig -> String
showIsaIT ident i theory = showIsaT ident theory ++ "_" ++ show i

replaceChar1 :: Char -> String
replaceChar1 c | isIsaChar c = [c] 
               | otherwise = replaceChar c++"X"

transString :: String -> String
transString "" = "X"
transString (c:s) = 
   if isInf (c:s) then concatMap replaceChar1 $ cut (c:s)
     else (if isAlpha c && isAscii c then [c] 
              else 'X':replaceChar1 c) ++ concatMap replaceChar1 s

isInf :: String -> Bool
isInf s = has2Under s && has2Under (reverse s)

has2Under :: String -> Bool
has2Under (fs:sn:_) = fs == '_' && sn == '_'
has2Under _ = False

cut :: String -> String
cut = reverse . tail . tail . reverse . tail . tail

-- Replacement of special characters

replaceChar :: Char -> String
replaceChar c = if isIsaChar c then [c] else 
                Map.findWithDefault "_" c $ Map.fromList 
 [('!' , "Exclam"),
  ('#' , "Sharp"),
  ('$' , "Dollar"),
  ('%' , "Percent"),
  ('&' , "Amp"),
  ('(' , "OBra"),
  (')' , "CBra"),
  ('*' , "x"),
  ('+' , "Plus"),
  (',' , "Comma"),
  ('-' , "Minus"),
  ('.' , "Dot"),
  ('/' , "Div"),
  (':' , "Colon"),
  (';' , "Semi"),
  ('<' , "Lt"),
  ('=' , "Eq"),
  ('>' , "Gt"),
  ('?' , "Q"),
  ('@' , "At"),
  ('\\' , "Back"),
  ('^' , "Hat"),
  ('`' , "'"),
  ('{' , "Cur"),
  ('|' , "Bar"),
  ('}' , "Ruc"),
  ('~' , "Tilde"),
  ('\128' , "A1"),
  ('\129' , "A2"),
  ('\130' , "A3"),
  ('\131' , "A4"),
  ('\132' , "A5"),
  ('\133' , "A6"),
  ('\134' , "AE"),
  ('\135' , "C"),
  ('\136' , "E1"),
  ('\137' , "E2"),
  ('\138' , "E3"),
  ('\139' , "E4"),
  ('\140' , "I1"),
  ('\141' , "I2"),
  ('\142' , "I3"),
  ('\143' , "I4"),
  ('\144' , "D1"),
  ('\145' , "N1"),
  ('\146' , "O1"),
  ('\147' , "O2"),
  ('\148' , "O3"),
  ('\149' , "O4"),
  ('\150' , "O5"),
  ('\151' , "x"),
  ('\152' , "O"),
  ('\153' , "U1"),
  ('\154' , "U2"),
  ('\155' , "U3"),
  ('\156' , "U4"),
  ('\157' , "Y"),
  ('\158' , "F"),
  ('\159' , "ss"),
  ('¡' , "SpanishExclam"),
  ('¢' , "c"),
  ('£' , "Lb"),
  ('¤' , "o"),
  ('¥' , "Yen"),
  ('¦' , "Bar1"),
  ('§' , "Paragraph"),
  ('¨' , "\'"),
  ('©' , "Copyright"),
  ('ª' , "a1"),
  ('«' , "\'"),
  ('¬' , "not"),
  ('­' , "Minus1"),
  ('®' , "Regmark"),
  ('°' , "Degree"),
  ('±' , "Plusminus"),
  ('²' , "2"),
  ('³' , "3"),
  ('´' , "'"),
  ('µ' , "Mu"),
  ('¶' , "q"),
  ('·' , "Dot"),
  ('¸' , "'"),
  ('¹' , "1"),
  ('º' , "2"),
  ('»' , "\'"),
  ('¼' , "Quarter"),
  ('½' , "Half"),
  ('¾' , "Threequarter"),
  ('¿' , "Q"),
  ('À' , "A7"),
  ('Á' , "A8"),
  ('Â' , "A9"),
  ('Ã' , "A10"),
  ('Ä' , "A11"),
  ('Å' , "A12"),
  ('Æ' , "AE2"),
  ('Ç' , "C2"),
  ('È' , "E5"),
  ('É' , "E6"),
  ('Ê' , "E7"),
  ('Ë' , "E8"),
  ('Ì' , "I5"),
  ('Í' , "I6"),
  ('Î' , "I7"),
  ('Ï' , "I8"),
  ('Ð' , "D2"),
  ('Ñ' , "N2"),
  ('Ò' , "O6"),
  ('Ó' , "O7"),
  ('Ô' , "O8"),
  ('Õ' , "O9"),
  ('Ö' , "O10"),
  ('×' , "xx"),
  ('Ø' , "011"),
  ('Ù' , "U5"),
  ('Ú' , "U6"),
  ('Û' , "U7"),
  ('Ü' , "U8"),
  ('Ý' , "Y"),
  ('Þ' , "F"),
  ('ß' , "ss"),
  ('à' , "a2"),
  ('á' , "a3"),
  ('â' , "a4"),
  ('ã' , "a5"),
  ('ä' , "a6"),
  ('å' , "a7"),
  ('æ' , "ae"),
  ('ç' , "c"),
  ('è' , "e1"),
  ('é' , "e2"),
  ('ê' , "e3"),
  ('ë' , "e4"),
  ('ì' , "i1"),
  ('í' , "i2"),
  ('î' , "i3"),
  ('ï' , "i4"),
  ('ð' , "d"),
  ('ñ' , "n"),
  ('ò' , "o1"),
  ('ó' , "o2"),
  ('ô' , "o3"),
  ('õ' , "o4"),
  ('ö' , "o5"),
  ('÷' , "Div1"),
  ('ø' , "o6"),
  ('ù' , "u1"),
  ('ú' , "u2"),
  ('û' , "u3"),
  ('ü' , "u4"),
  ('ý' , "y5"),
  ('þ' , "f"),
  ('ÿ' , "y")]

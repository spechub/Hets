{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Printing functions for Isabelle logic.
-}

module Isabelle.IsaPrint where

import Common.Id 
import Common.PrettyPrint

import Data.Char

showIsa :: Id -> String
showIsa = transString . flip showPretty ""

showIsaSid :: SIMPLE_ID -> String
showIsaSid = transString . flip showPretty ""

-- disambiguation of overloaded ids
showIsaI :: Id -> Int -> String
showIsaI ident i = showIsa ident ++ "__" ++ show i


-- Replacement of special characters

replaceChar :: Char -> String
replaceChar '\t' = "_"
replaceChar '\n' = "_"
replaceChar '\r' = "_"
replaceChar ' ' = "_"
replaceChar '!' = "Exclam"
replaceChar '\"' = "_"
replaceChar '#' = "Sharp"
replaceChar '$' = "Dollar"
replaceChar '%' = "Percent"
replaceChar '&' = "Amp"
replaceChar '(' = "OBra"
replaceChar ')' = "CBra"
replaceChar '*' = "x"
replaceChar '+' = "Plus"
replaceChar ',' = "Comma"
replaceChar '-' = "Minus"
replaceChar '.' = "Dot"
replaceChar '/' = "Div"
replaceChar ':' = "Colon"
replaceChar ';' = "Semi"
replaceChar '<' = "Lt"
replaceChar '=' = "Eq"
replaceChar '>' = "Gt"
replaceChar '?' = "Q"
replaceChar '@' = "At"
replaceChar '[' = "_"
replaceChar '\\' = "Back"
replaceChar ']' = "_"
replaceChar '^' = "Hat"
replaceChar '`' = "'"
replaceChar '{' = "Cur"
replaceChar '|' = "Bar"
replaceChar '}' = "Ruc"
replaceChar '~' = "Tilde"
replaceChar '\128' = "A1"
replaceChar '\129' = "A2"
replaceChar '\130' = "A3"
replaceChar '\131' = "A4"
replaceChar '\132' = "A5"
replaceChar '\133' = "A6"
replaceChar '\134' = "AE"
replaceChar '\135' = "C"
replaceChar '\136' = "E1"
replaceChar '\137' = "E2"
replaceChar '\138' = "E3"
replaceChar '\139' = "E4"
replaceChar '\140' = "I1"
replaceChar '\141' = "I2"
replaceChar '\142' = "I3"
replaceChar '\143' = "I4"
replaceChar '\144' = "D1"
replaceChar '\145' = "N1"
replaceChar '\146' = "O1"
replaceChar '\147' = "O2"
replaceChar '\148' = "O3"
replaceChar '\149' = "O4"
replaceChar '\150' = "O5"
replaceChar '\151' = "x"
replaceChar '\152' = "O"
replaceChar '\153' = "U1"
replaceChar '\154' = "U2"
replaceChar '\155' = "U3"
replaceChar '\156' = "U4"
replaceChar '\157' = "Y"
replaceChar '\158' = "F"
replaceChar '\159' = "ss"
replaceChar '\160' = "_"
replaceChar '¡' = "SpanishExclam"
replaceChar '¢' = "c"
replaceChar '£' = "Lb"
replaceChar '¤' = "o"
replaceChar '¥' = "Yen"
replaceChar '¦' = "Bar1"
replaceChar '§' = "Paragraph"
replaceChar '¨' = "\""
replaceChar '©' = "Copyright"
replaceChar 'ª' = "a1"
replaceChar '«' = "\""
replaceChar '¬' = "not"
replaceChar '­' = "Minus1"
replaceChar '®' = "Regmark"
replaceChar '¯' = "_"
replaceChar '°' = "Degree"
replaceChar '±' = "Plusminus"
replaceChar '²' = "2"
replaceChar '³' = "3"
replaceChar '´' = "'"
replaceChar 'µ' = "Mu"
replaceChar '¶' = "q"
replaceChar '·' = "Dot"
replaceChar '¸' = "'"
replaceChar '¹' = "1"
replaceChar 'º' = "2"
replaceChar '»' = "\""
replaceChar '¼' = "Quarter"
replaceChar '½' = "Half"
replaceChar '¾' = "Threequarter"
replaceChar '¿' = "Q"
replaceChar 'À' = "A7"
replaceChar 'Á' = "A8"
replaceChar 'Â' = "A9"
replaceChar 'Ã' = "A10"
replaceChar 'Ä' = "A11"
replaceChar 'Å' = "A12"
replaceChar 'Æ' = "AE2"
replaceChar 'Ç' = "C2"
replaceChar 'È' = "E5"
replaceChar 'É' = "E6"
replaceChar 'Ê' = "E7"
replaceChar 'Ë' = "E8"
replaceChar 'Ì' = "I5"
replaceChar 'Í' = "I6"
replaceChar 'Î' = "I7"
replaceChar 'Ï' = "I8"
replaceChar 'Ð' = "D2"
replaceChar 'Ñ' = "N2"
replaceChar 'Ò' = "O6"
replaceChar 'Ó' = "O7"
replaceChar 'Ô' = "O8"
replaceChar 'Õ' = "O9"
replaceChar 'Ö' = "O10"
replaceChar '×' = "xx"
replaceChar 'Ø' = "011"
replaceChar 'Ù' = "U5"
replaceChar 'Ú' = "U6"
replaceChar 'Û' = "U7"
replaceChar 'Ü' = "U8"
replaceChar 'Ý' = "Y"
replaceChar 'Þ' = "F"
replaceChar 'ß' = "ss"
replaceChar 'à' = "a2"
replaceChar 'á' = "a3"
replaceChar 'â' = "a4"
replaceChar 'ã' = "a5"
replaceChar 'ä' = "a6"
replaceChar 'å' = "a7"
replaceChar 'æ' = "ae"
replaceChar 'ç' = "c"
replaceChar 'è' = "e1"
replaceChar 'é' = "e2"
replaceChar 'ê' = "e3"
replaceChar 'ë' = "e4"
replaceChar 'ì' = "i1"
replaceChar 'í' = "i2"
replaceChar 'î' = "i3"
replaceChar 'ï' = "i4"
replaceChar 'ð' = "d"
replaceChar 'ñ' = "n"
replaceChar 'ò' = "o1"
replaceChar 'ó' = "o2"
replaceChar 'ô' = "o3"
replaceChar 'õ' = "o4"
replaceChar 'ö' = "o5"
replaceChar '÷' = "Div1"
replaceChar 'ø' = "o6"
replaceChar 'ù' = "u1"
replaceChar 'ú' = "u2"
replaceChar 'û' = "u3"
replaceChar 'ü' = "u4"
replaceChar 'ý' = "y5"
replaceChar 'þ' = "f"
replaceChar 'ÿ' = "y"
replaceChar  _ = "_"

isIsaChar :: Char -> Bool
isIsaChar c = (isAlphaNum c && isAscii c) || c `elem` "_'"


replaceChar1 :: Char -> String
replaceChar1 c | isIsaChar c = [c] 
               | otherwise = replaceChar c++"__"

transString :: String -> String
transString "" = "X"
transString (c:s) = 
  (if isAlpha c && isAscii c then [c] else 'X':replaceChar1 c)
   ++ (concat $ map replaceChar1 s)



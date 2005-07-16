{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

translate 'Id' to Isabelle strings
-}

module Isabelle.Translate (showIsaT, showIsaIT, transStringT, 
                           transString, isaPrelude,
                           charMap) where

import Common.Id 
import Common.ProofUtils

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Data.Char

import Isabelle.IsaSign
import Isabelle.IsaStrings

------------------- Id translation functions -------------------
isaPrelude :: Map.Map BaseSig (Set.Set String)
isaPrelude = Map.fromList 
  [(HsHOLCF_thy, Set.insert "fliftbin" holcfS),
   (MainHC_thy, foldr Set.insert mainS ["pApp","apt","app","defOp","pair"]),
   (Main_thy, mainS), (HOLCF_thy, holcfS), 
   (HOL_thy, holS), (Pure_thy, pureS)]

showIsaT :: Id -> BaseSig -> String 
showIsaT ide thy = let 
    rdru = reverse . dropWhile (== '_') 
    tr = transStringT thy
    str = show ide 
    in if isInfix2 ide then "" {-"XX"-}  ++ tr (rdru $ rdru str) else tr str
    -- otherwise cutting off may lead to a name clash!

showIsaIT :: Id -> Int -> BaseSig -> String
showIsaIT ident i theory = showIsaT ident theory ++ "_" ++ show i

transStringT :: BaseSig -> String -> String
transStringT i s = let t = transString s in
  if Set.member t $ maybe (error "Isabelle.Translate.transStringT") id 
         $ Map.lookup i isaPrelude 
  then t ++ "" {-"X"-} else t

-- | check for legal alphanumeric isabelle characters
isIsaChar :: Char -> Bool
isIsaChar c = isAlphaNum c && isAscii c || c `elem` "_'"

transString :: String -> String
transString str = let 
    x = 'U'
    replaceChar1 d | d == x = "YU"  -- code out existing U!
                   | isIsaChar d = [d] 
                   | otherwise = replaceChar d ++ [x]
    in case str of 
    "" -> [x]
    c : s -> let l = replaceChar1 c in 
             (if isDigit c || c `elem` "_'" then [x, c]
             else l) ++ concatMap replaceChar1 s

-- | injective replacement of special characters
replaceChar :: Char -> String
-- <http://www.htmlhelp.com/reference/charset/>
replaceChar c = if isIsaChar c then [c] else let n = ord c in 
    if n <= 32 || n >= 127 && n < 160 || n > 255 then "Slash_" ++ show n 
    else maybe (error "Isabelle.replaceChar") id $ Map.lookup c charMap


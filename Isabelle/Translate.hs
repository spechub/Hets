{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

translate 'Id' to Isabelle strings
-}

module Isabelle.Translate (showIsaConstT, showIsaConstIT, 
			  showIsaTypeT, showIsaTypeIT,
			   --showIsaT, showIsaIT,
			   transConstStringT, transTypeStringT,
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
data IsaPreludes = IsaPreludes 
    {preTypes :: Map.Map BaseSig (Set.Set String),
     preConsts :: Map.Map BaseSig (Set.Set String)}

isaPrelude :: IsaPreludes
isaPrelude = IsaPreludes {
  preTypes = Map.fromList 
  [(HsHOLCF_thy, types holcfS), (MainHC_thy, types mainS),
   (Main_thy, types mainS), (HOLCF_thy, types holcfS), 
   (HOL_thy, types holS), (Pure_thy, types pureS)],
  preConsts = Map.fromList 
  [(HsHOLCF_thy, Set.insert "fliftbin" (consts holcfS)),
   (MainHC_thy, foldr Set.insert  (consts mainS) ["pApp","apt","app","defOp","pair"]),
   (Main_thy,  consts mainS), (HOLCF_thy, consts holcfS), 
   (HOL_thy,  consts holS), (Pure_thy, consts pureS)]}

--showIsaT :: Id -> BaseSig -> String 
--showIsaT ide thy = let 
--    rdru = reverse . dropWhile (== '_') 
--    tr = transTypeStringT thy
--    str = show ide
--    in if isInfix2 ide then "XX" ++ tr (rdru $ rdru str) else tr str
    -- otherwise cutting off may lead to a name clash!

--showIsaIT :: Id -> Int -> BaseSig -> String
--showIsaIT ident i theory = showIsaT ident theory ++ "_" ++ show i

showIsaT1 :: (String -> String) -> Id -> String
showIsaT1 tr ide = let
    rdru = reverse . dropWhile (== '_') 
    str = show ide
    in if isInfix2 ide then "XX" ++ tr (rdru $ rdru str) else tr str
    -- otherwise cutting off may lead to a name clash!

showIsaConstT :: Id -> BaseSig -> String 
showIsaConstT ide thy = showIsaT1 (transConstStringT thy) ide
showIsaTypeT :: Id -> BaseSig -> String 
showIsaTypeT ide thy = showIsaT1 (transTypeStringT thy) ide

showIsaConstIT :: Id -> Int -> BaseSig -> String
showIsaConstIT ident i theory = showIsaConstT ident theory ++ "_" ++ show i
showIsaTypeIT :: Id -> Int -> BaseSig -> String
showIsaTypeIT ident i theory = showIsaTypeT ident theory ++ "_" ++ show i

--transOldStringT :: BaseSig -> String -> String
--transOldStringT i s = let t = transString s in
--  if Set.member t $ maybe (error "Isabelle.Translate.transStringT") id 
--         $ Map.lookup i (preConsts isaPrelude)
--  then t++"X" else t -- ++ "X" else t

transConstStringT :: BaseSig -> String -> String
transConstStringT i s = let t = transString s in
  if Set.member t $ maybe (error "Isabelle.Translate.transStringT") id 
         $ Map.lookup i (preConsts isaPrelude)
  then t++"X" else t -- ++ "X" else t

transTypeStringT :: BaseSig -> String -> String
transTypeStringT i s = let t = transString s in
  if Set.member t $ maybe (error "Isabelle.Translate.transStringT") id 
         $ Map.lookup i (preTypes isaPrelude)
  then t++"X" else t -- ++ "X" else t


-- | check for legal alphanumeric isabelle characters
isIsaChar :: Char -> Bool
isIsaChar c = isAlphaNum c && isAscii c || c `elem` "_'"

transString :: String -> String
transString str = let 
    x = 'X'
    replaceChar1 d | d == x = "YX"  -- code out existing X!
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

{- |
Module      :  ./Isabelle/Translate.hs
Description :  create legal Isabelle mixfix identifier
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

translate 'Id' to Isabelle strings
-}

module Isabelle.Translate
    ( showIsaConstT, showIsaConstIT, showIsaTypeT, transConstStringT
    , transTypeStringT
    , mkIsaConstT, mkIsaConstIT, transString, isaPrelude
    , IsaPreludes (..)
    , getConstIsaToks ) where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.ProofUtils
import Common.Utils
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Char
import Data.Maybe
import Data.List

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Isabelle.IsaStrings

-- ----------------- Id translation functions -------------------
data IsaPreludes = IsaPreludes
  { preTypes :: Map.Map BaseSig (Set.Set String)
  , preConsts :: Map.Map BaseSig (Set.Set String) }

isaKeyset :: Set.Set String
isaKeyset = Set.fromList isaKeywords

mkPreludeMap :: [(BaseSig, Set.Set String)] -> Map.Map BaseSig (Set.Set String)
mkPreludeMap = Map.fromList . map (\ (b, s) -> (b, Set.union s isaKeyset))

hc2isaNames :: [String]
hc2isaNames =
  [ defOpS, "mapSnd", "mapFst", "lift2partial", "lift2bool"
  , "lift2unit", "liftUnit", "liftUnit2partial", "liftUnit2bool"
  , "liftUnit2unit", "bool2partial", "curryOp", "uncurryOp", "unpack2bool"
  , "partial2bool", "unpack2partial", "unpackBool", "unpackPartial"
  , "resOp", "whenElseOp", "exEqualOp", "existEqualOp", "ifImplOp", "flip"
  , "makePartial", "makeTotal", "noneOp", "strongEqualOp", "restrictOp"]

isaPrelude :: IsaPreludes
isaPrelude = IsaPreludes
  { preTypes = mkPreludeMap
      [ (HsHOL_thy, types mainS)
      , (HsHOLCF_thy, types holcfS)
      , (MainHC_thy, types mainS)
      , (MainHCPairs_thy, types mainS)
      , (Main_thy, types mainS)
      , (HOLCF_thy, types holcfS)]
  , preConsts = mkPreludeMap
      [ (HsHOL_thy, consts mainS)
      , (HsHOLCF_thy, Set.insert fliftbinS (consts holcfS))
      , (MainHC_thy, foldr Set.insert (consts mainS)
         $ [ pAppS, aptS, appS, pairC ] ++ hc2isaNames)
      , (MainHCPairs_thy, foldr Set.insert (consts mainS) hc2isaNames)
      , (Main_thy, consts mainS), (HOLCF_thy, consts holcfS)]}

getAltTokenList :: String -> Int -> Id -> BaseSig -> [Token]
getAltTokenList newPlace over i@(Id ms cs qs) thy = let
    (fs, ps) = splitMixToken ms
    nonPlaces = filter (not . isPlace) fs
    constSet = Map.findWithDefault Set.empty thy $ preConsts isaPrelude
    over2 = isSingle nonPlaces && Set.member (tokStr $ head nonPlaces)
            constSet || Set.member (show i) constSet
    o1 = if over2 && over == 0 then over + 1 else over
    newFs =
      let (fps, rts) = span isPlace fs in case rts of
        hd : tl | o1 > 0 -> fps ++ mkSimpleId (tokStr hd ++
            if o1 < 3 then replicate o1 '\'' else '_' : show o1)
                  : tl
        _ -> fs
    in getTokenList newPlace $ Id (newFs ++ ps) cs qs

toAltSyntax :: Bool -> Int -> GlobalAnnos -> Int -> Id -> BaseSig
            -> Set.Set String -> Maybe AltSyntax
toAltSyntax prd over ga n i thy toks = let
    (precMap, mx) = Rel.toPrecMap $ prec_annos ga
    minPrec = if prd then 42 else 52
    adjustPrec p = 2 * p + minPrec
    br = "/ "
    newPlace = br ++ "_"
    minL = replicate n lowPrio
    minL1 = tail minL
    minL2 = tail minL1
    ni = placeCount i
    atoks@(hd : tl) = getAltTokenList newPlace over i thy
    compoundToks = map (: []) ",[]{}"
    convert Token { tokStr = s } =
      if elem s $ newPlace : compoundToks then s else br ++ quote s
    tts = concatMap convert tl
    ht = let chd = convert hd in
      if isPrefixOf br chd then drop (length br) chd else chd
    ts = ht ++ tts
    (precList, erg)
      | isInfix i = case Map.lookup i precMap of
        Just p -> let
            q = adjustPrec p
            (l, r) = case Map.lookup i $ assoc_annos ga of
                 Nothing -> (q + 1, q + 1)
                 Just ALeft -> (q, q + 1)
                 Just ARight -> (q + 1, q)
            in (l : minL2 ++ [r], q)
        Nothing -> let q = adjustPrec $ mx + 1 in (q : minL2 ++ [q], minPrec)
      | begPlace i = let q = adjustPrec $ mx + 3 in (q : minL1 , q)
      | endPlace i = let q = adjustPrec $ mx + 2 in (minL1 ++ [q], q)
      | otherwise = (minL, maxPrio - 1)
    in if n < 0 || ni > 1 && ni /= n
           || any (flip Set.member toks . tokStr) atoks then Nothing
       else Just $ if n == 0 then AltSyntax ts [] maxPrio
       else if isMixfix i then AltSyntax
                ('(' : ts ++ ")") precList erg
       else AltSyntax
            (ts ++ "/'(" ++
                   concat (replicate (n - 1) "_,/ ")
                   ++ "_')") (replicate n 3) $ maxPrio - 1

quote :: String -> String
quote l = case l of
    [] -> l
    c : r -> (if elem c "_/'()" then '\'' : [c]
              else if elem c "\\\"" then '\\' : [c] else [c]) ++ quote r

showIsaT1 :: (String -> String) -> Id -> String
showIsaT1 tr ide = let
    str = tr $ show ide
    in if null str then error "showIsaT1" else if
       elem (last str) "_" then str ++ "X" else str

showIsaConstT :: Id -> BaseSig -> String
showIsaConstT ide thy = showIsaT1 (transConstStringT thy) ide

-- also pass number of arguments
mkIsaConstT :: Bool -> GlobalAnnos -> Int -> Id -> BaseSig -> Set.Set String
            -> VName
mkIsaConstT = mkIsaConstVName 0 showIsaConstT

mkIsaConstVName :: Int -> (Id -> BaseSig -> String) -> Bool -> GlobalAnnos
                -> Int -> Id -> BaseSig -> Set.Set String -> VName
mkIsaConstVName over f prd ga n ide thy toks =
  let s = f ide thy
      a = toAltSyntax prd over ga n ide thy toks
 in if n == 0 && case a of
      Just (AltSyntax as [] _) -> as == s
      _ -> False then VName { new = s, altSyn = Nothing }
    else VName
  { new = (if n < 0 || isMixfix ide || s /= show ide then id else ("X_" ++)) s
  , altSyn = a }

showIsaTypeT :: Id -> BaseSig -> String
showIsaTypeT ide thy = showIsaT1 (transTypeStringT thy) ide

-- | add a number for overloading
showIsaConstIT :: Id -> Int -> BaseSig -> String
showIsaConstIT ide i thy = showIsaConstT ide thy ++ "X" ++ show i

mkIsaConstIT :: Bool -> GlobalAnnos -> Int -> Id -> Int -> BaseSig
             -> Set.Set String -> VName
mkIsaConstIT prd ga n ide i =
    mkIsaConstVName i (`showIsaConstIT` i) prd ga n ide

{- | get the tokens of the alternative syntax that should not be used
     as variables -}
getConstIsaToks :: Id -> Int -> BaseSig -> Set.Set String
getConstIsaToks ide i thy = if i < 2 then
   Set.union (getConstIsaToksAux ide 0 thy) (getConstIsaToksAux ide 1 thy)
   else getConstIsaToksAux ide i thy

getConstIsaToksAux :: Id -> Int -> BaseSig -> Set.Set String
getConstIsaToksAux ide i =
   foldr (Set.insert . tokStr)
             Set.empty . getAltTokenList "" i ide

transIsaInternalName :: String -> String
transIsaInternalName s = if last s == '_' then s ++ "X" else s

transIsaStringT :: Map.Map BaseSig (Set.Set String) -> BaseSig
                -> String -> String
transIsaStringT m i s = let t = transStringAux False s in
  transIsaInternalName $ if Set.member t
    $ fromMaybe (error "Isabelle.transIsaStringT") $ Map.lookup i m
  then transIsaStringT m i $ '_' : s else t

transConstStringT :: BaseSig -> String -> String
transConstStringT = transIsaStringT $ preConsts isaPrelude

transTypeStringT :: BaseSig -> String -> String
transTypeStringT = transIsaStringT $ preTypes isaPrelude

-- | check for legal alphanumeric Isabelle characters
isIsaChar :: Char -> Bool
isIsaChar c = isAlphaNum c && isAscii c || elem c "_'"

-- | translate to a valid Isabelle string possibly non-injectively
transString :: String -> String
transString = transStringAux True

-- | if true don't try to be injective
transStringAux :: Bool -> String -> String
transStringAux b str = let
    x = 'X'
    replaceChar1 d | not b && d == x = [x, x]  -- code out existing X!
                   | b && d == ' ' = "_"
                   | isIsaChar d = [d]
                   | otherwise = x : replaceChar d
    in case str of
    "" -> error "transString"
    c : s -> let l = replaceChar1 c in
             (if isDigit c || elem c "_'" then [x, c]
             else l) ++ concatMap replaceChar1
        (if b then replace "' '" "'Space'" s else s)

-- | injective replacement of special characters
replaceChar :: Char -> String
-- <http://www.htmlhelp.com/reference/charset/>
replaceChar c = if isIsaChar c then [c] else let n = ord c in
    if n <= 32 || n >= 127 && n < 160 || n > 255 then "Slash_" ++ show n
    else lookupCharMap c

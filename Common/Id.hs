{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/Id.hs
Description :  positions, simple and mixfix identifiers
Copyright   :  (c) Klaus Luettich and Christian Maeder and Uni Bremen 2002-2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

This module supplies positions, simple and mixfix identifiers.
A simple identifier is a lexical token given by a string and a start position.

-  A 'place' is a special token within mixfix identifiers.

-  A mixfix identifier may have a compound list.
   This compound list follows the last non-place token!

-  Identifiers fixed for all logics
-}

module Common.Id where

import Data.Char
import Data.Data
import Data.List (isPrefixOf)
import Data.Ratio
import qualified Data.Set as Set

-- do use in data types that derive d directly
data Pos = SourcePos
  { sourceName :: String
  , sourceLine :: !Int
  , sourceColumn :: !Int
  } deriving (Eq, Ord, Typeable, Data)

instance Show Pos where
    showsPrec _ = showPos

-- | position lists with trivial equality
newtype Range = Range { rangeToList :: [Pos] }
  deriving (Typeable, Data)

-- let InlineAxioms recognize positions
instance Show Range where
    show _ = "nullRange"

-- ignore all ranges in comparisons
instance Eq Range where
    _ == _ = True

-- Ord must be consistent with Eq
instance Ord Range where
   compare _ _ = EQ

nullRange :: Range
nullRange = Range []

isNullRange :: Range -> Bool
isNullRange = null . rangeToList

appRange :: Range -> Range -> Range
appRange (Range l1) (Range l2) = Range $ l1 ++ l2

concatMapRange :: (a -> Range) -> [a] -> Range
concatMapRange f = Range . concatMap (rangeToList . f)

-- | construct a new position
newPos :: String -> Int -> Int -> Pos
newPos = SourcePos

-- | increment the column counter
incSourceColumn :: Pos -> Int -> Pos
incSourceColumn (SourcePos s l c) = SourcePos s l . (c +)

-- | show a position
showPos :: Pos -> ShowS
showPos p = let name = sourceName p
                line = sourceLine p
                column = sourceColumn p
            in noShow (null name) (showString name . showChar ':') .
               noShow (line == 0 && column == 0)
                          (shows line . showChar '.' . shows column)

-- * Tokens as 'String's with positions that are ignored for 'Eq' and 'Ord'

-- | tokens as supplied by the scanner
data Token = Token { tokStr :: String
                   , tokPos :: Range
                   } deriving (Eq, Ord, Typeable, Data)

instance Show Token where
  show = tokStr

instance Read Token where
  readsPrec i = map (\ (a, r) -> (mkSimpleId a, r)) . readsPrec i

-- | simple ids are just tokens
type SIMPLE_ID = Token

-- | construct a token without position from a string
mkSimpleId :: String -> Token
mkSimpleId s = Token s nullRange

-- | null token
nullTok :: Token
nullTok = mkSimpleId ""

-- | create a numbered string
mkNumStr :: String -> Int -> String
mkNumStr str n = str ++ show n

-- | create a numbered simple identifier (for variables)
mkNumVar :: String -> Int -> Token
mkNumVar str = mkSimpleId . mkNumStr str

-- | test if the first character indicates a legal simple CASL identifier
isSimpleToken :: Token -> Bool
isSimpleToken t = case tokStr t of
    c : r -> isAlpha c || isDigit c && null r || c == '\''
    "" -> False

-- | collect positions
catPosAux :: [Token] -> [Pos]
catPosAux = concatMap (rangeToList . getRange)

-- | collect positions as range
catRange :: [Token] -> Range
catRange = Range . catPosAux

-- | shortcut to get positions of surrounding and interspersed tokens
toRange :: Token -> [Token] -> Token -> Range
toRange o l c = catRange $ o : l ++ [c]

-- * placeholder stuff

-- | the special 'place'
place :: String
place = "__"

-- | is a 'place' token
isPlace :: Token -> Bool
isPlace (Token t _) = t == place

placeTok :: Token
placeTok = mkSimpleId place

-- * equality symbols

-- | also a definition indicator
equalS :: String
equalS = "="

-- | mind spacing i.e. in @e =e= e@
exEqual :: String
exEqual = "=e="

-- | token for type annotations
typeTok :: Token
typeTok = mkSimpleId ":"

-- * mixfix identifiers with compound lists and its range

-- | mixfix and compound identifiers
data Id = Id
    { getTokens :: [Token]
    , getComps :: [Id]
    , rangeOfId :: Range }
    deriving (Eq, Ord, Typeable, Data)
    -- pos of square brackets and commas of a compound list

instance Show Id where
  showsPrec _ = showId

-- | construct an 'Id' from a token list
mkId :: [Token] -> Id
mkId toks = Id toks [] nullRange

mkInfix :: String -> Id
mkInfix s = mkId [placeTok, mkSimpleId s, placeTok]

-- | a prefix for generated names
genNamePrefix :: String
genNamePrefix = "gn_"

-- | create a generated simple identifier
genToken :: String -> Token
genToken = mkSimpleId . (genNamePrefix ++)

-- | create a generated, numbered variable
genNumVar :: String -> Int -> Token
genNumVar str = genToken . mkNumStr str

-- | create a generated identifier
genName :: String -> Id
genName str = mkId [genToken str]

-- | create a generated identifier from a given one excluding characters
mkGenName :: Id -> Id
mkGenName i@(Id ts cs r) = case ts of
  t : s -> let st = tokStr t in case st of
    c : _ | isAlphaNum c -> Id (genToken st : s) cs r
          | isPlace t -> Id (mkSimpleId "gn" : ts) cs r
          | c == '\'' -> i
    _ -> Id (mkSimpleId "gn_n" : ts) cs r
  _ -> i

-- | tests whether a Token is already a generated one
isGeneratedToken :: Token -> Bool
isGeneratedToken = isPrefixOf genNamePrefix . tokStr

{- | append a number to the first token of a (possible compound) Id,
   or generate a new identifier for /invisible/ ones -}
appendString :: Id -> String -> Id
appendString (Id tokList idList range) s = let
  isAlphaToken tok = case tokStr tok of
    c : _ -> isAlpha c
    "" -> False
  genTok tList tList1 str = case tList of
    [] -> [mkSimpleId $ genNamePrefix ++ "n" ++ str]
          -- for invisible identifiers
    tok : tokens ->
       if isPlace tok || not (isAlphaToken tok)
       then genTok tokens (tok : tList1) str
       else reverse tList1 ++
           [tok {tokStr = -- avoid gn_gn_
                (if isGeneratedToken tok then "" else genNamePrefix)
                 ++ tokStr tok ++ str}]
                 {- only underline words may be
                    prefixed with genNamePrefix or extended with a number -}
           ++ tokens
 in Id (genTok tokList [] s) idList range

-- | the name of injections
injToken :: Token
injToken = genToken "inj"

injName :: Id
injName = mkId [injToken]

mkUniqueName :: Token -> [Id] -> Id
mkUniqueName t is =
    Id [foldl (\ (Token s1 r1) (Token s2 r2) ->
                Token (s1 ++ "_" ++ s2) $ appRange r1 r2) t
        $ concatMap getTokens is]
    (let css = filter (not . null) $ map getComps is
     in case css of
          [] -> []
          h : r -> if all (== h) r then h else concat css)
    (foldl appRange nullRange $ map rangeOfId is)

-- | the name of projections
projToken :: Token
projToken = genToken "proj"

projName :: Id
projName = mkId [projToken]

mkUniqueProjName :: Id -> Id -> Id
mkUniqueProjName from to = mkUniqueName projToken [from, to]

mkUniqueInjName :: Id -> Id -> Id
mkUniqueInjName from to = mkUniqueName injToken [from, to]

isInjName :: Id -> Bool
isInjName = isPrefixOf (show injName) . show

-- | the postfix type identifier
typeId :: Id
typeId = mkId [placeTok, typeTok]

-- | the invisible application rule with two places
applId :: Id
applId = mkId [placeTok, placeTok]

-- | the infix equality identifier
eqId :: Id
eqId = mkInfix equalS

exEq :: Id
exEq = mkInfix exEqual

-- ** show stuff

-- | shortcut to suppress output for input condition
noShow :: Bool -> ShowS -> ShowS
noShow b s = if b then id else s

-- | intersperse seperators
showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList s f l = case l of
  [] -> id
  [x] -> f x
  x : r -> f x . s . showSepList s f r

-- | shows a compound list
showIds :: [Id] -> ShowS
showIds is = noShow (null is) $ showString "["
             . showSepList (showString ",") showId is
             . showString "]"

-- | shows an 'Id', puts final places behind a compound list
showId :: Id -> ShowS
showId (Id ts is _) =
        let (toks, places) = splitMixToken ts
            showToks = showSepList id $ showString . tokStr
        in showToks toks . showIds is . showToks places

-- ** splitting identifiers

-- | splits off the front and final places
splitMixToken :: [Token] -> ([Token], [Token])
splitMixToken ts = case ts of
  [] -> ([], [])
  h : l ->
    let (toks, pls) = splitMixToken l
        in if isPlace h && null toks
           then (toks, h : pls)
           else (h : toks, pls)

{- | return open and closing list bracket and a compound list
   from a bracket 'Id'  (parsed by 'Common.AnnoParser.caslListBrackets') -}
getListBrackets :: Id -> ([Token], [Token], [Id])
getListBrackets (Id b cs _) =
    let (b1, rest) = break isPlace b
        b2 = if null rest then []
             else filter (not . isPlace) rest
    in (b1, b2, cs)

-- ** reconstructing token lists

{- | reconstruct a list with surrounding strings and interspersed
     commas with proper position information that should be preserved
     by the input function -}
expandPos :: (Token -> a) -> (String, String) -> [a] -> Range -> [a]
{- expandPos f ("{", "}") [a,b] [(1,1), (1,3), 1,5)] =
   [ t"{" , a , t"," , b , t"}" ] where t = f . Token (and proper positions) -}
expandPos f (o, c) ts (Range ps) =
    if null ts then if null ps then map (f . mkSimpleId) [o, c]
       else map f (zipWith Token [o, c] [Range [head ps] , Range [last ps]])
    else let
      n = length ts + 1
      diff = n - length ps
      commas j = if j == 2 then [c] else "," : commas (j - 1)
      ocs = o : commas n
      hsep : tseps = map f
        $ if diff == 0
          then zipWith (\ s p -> Token s (Range [p])) ocs ps
          else map mkSimpleId ocs
    in hsep : concat (zipWith (\ t s -> [t, s]) ts tseps)

{- | reconstruct the token list of an 'Id'
   including square brackets and commas of (nested) compound lists. -}
getPlainTokenList :: Id -> [Token]
getPlainTokenList = getTokenList place

{- | reconstruct the token list of an 'Id'.
   Replace top-level places with the input String -}
getTokenList :: String -> Id -> [Token]
getTokenList placeStr (Id ts cs ps) =
    let convert = map (\ t -> if isPlace t then t {tokStr = placeStr} else t)
        {- reconstruct tokens of a compound list
           although positions will be replaced (by scan) -}
        getCompoundTokenList comps = concat .
            expandPos (: []) ("[", "]") (map getPlainTokenList comps)
    in if null cs then convert ts else
       let (toks, pls) = splitMixToken ts in
           convert toks ++ getCompoundTokenList cs ps ++ convert pls

-- ** conversion from 'SIMPLE_ID'

-- | a 'SIMPLE_ID' as 'Id'
simpleIdToId :: SIMPLE_ID -> Id
simpleIdToId sid = mkId [sid]

-- | a string as 'Id'
stringToId :: String -> Id
stringToId = simpleIdToId . mkSimpleId

-- | efficiently test for a singleton list
isSingle :: [a] -> Bool
isSingle l = case l of
    [_] -> True
    _ -> False

-- | test for a 'SIMPLE_ID'
isSimpleId :: Id -> Bool
isSimpleId (Id ts cs _) = null cs && case ts of
    [t] -> isSimpleToken t
    _ -> False

idToSimpleId :: Id -> Token
idToSimpleId i = case i of
  Id [t] [] _ -> t
  _ -> error $ "idToSimpleId: " ++ show i

-- ** fixity stuff

-- | number of 'place' in 'Id'
placeCount :: Id -> Int
placeCount (Id tops _ _) = length $ filter isPlace tops

-- | has a 'place'
isMixfix :: Id -> Bool
isMixfix (Id tops _ _) = any isPlace tops

-- | 'Id' starts with a 'place'
begPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)

-- | 'Id' ends with a 'place'
endPlace :: Id -> Bool
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

-- | starts with a 'place'
isPostfix :: Id -> Bool
isPostfix (Id tops _ _) = not (null tops) && isPlace (head tops)
                          && not (isPlace (last tops))

-- | starts and ends with a 'place'
isInfix :: Id -> Bool
isInfix (Id tops _ _) = not (null tops) && isPlace (head tops)
                        && isPlace (last tops)

-- * position stuff

-- | compute a meaningful position from an 'Id' for diagnostics
posOfId :: Id -> Range
posOfId (Id ts _ (Range ps)) =
   Range $ let l = filter (not . isPlace) ts
                       in catPosAux (if null l then ts
                       -- for invisible "__ __" (only places)
                          else l) ++ ps

-- | compute start and end position of a Token (or leave it empty)
tokenRange :: Token -> [Pos]
tokenRange (Token str (Range ps)) = case ps of
    [p] -> mkTokPos str p
    _ -> ps

mkTokPos :: String -> Pos -> [Pos]
mkTokPos str p = let l = length str in
      if l > 1 then [p, incSourceColumn p $ length str - 1] else [p]

outerRange :: Range -> [Pos]
outerRange (Range qs) = case qs of
  [] -> []
  q : _ -> let p = last qs in if p == q then [q] else [q, p]

sortRange :: [Pos] -> [Pos] -> [Pos]
sortRange rs qs = case qs of
  [] -> rs
  r : _ -> let
    ps = filter ((== sourceName r) . sourceName) rs
    p = minimum $ ps ++ qs
    q = maximum $ ps ++ qs
    in if p == q then [p] else [p, q]

joinRanges :: [[Pos]] -> [Pos]
joinRanges = foldr sortRange []

{- | compute start and end position of a declared Id (or leave it empty).
     Do not use for applied identifiers where place holders are replaced. -}
idRange :: Id -> [Pos]
idRange (Id ts _ r) =
    let (fs, rs) = splitMixToken ts
    in joinRanges $ map tokenRange fs ++ [outerRange r] ++ map tokenRange rs

-- -- helper class -------------------------------------------------------

{- | This class is derivable with DrIFT.
   Its main purpose is to have a function that operates on
   constructors with a 'Range' field. During parsing, mixfix
   analysis and ATermConversion this function might be very useful.
-}

class GetRange a where
    getRange :: a -> Range
    getRange = const nullRange
    rangeSpan :: a -> [Pos]
    rangeSpan = sortRange [] . getPosList

getPosList :: GetRange a => a -> [Pos]
getPosList = rangeToList . getRange

getRangeSpan :: GetRange a => a -> Range
getRangeSpan = Range . rangeSpan

instance GetRange Token where
    getRange = Range . tokenRange
    rangeSpan = tokenRange

instance GetRange Id where
    getRange = posOfId
    rangeSpan = idRange

instance GetRange Range where
    getRange = id
    rangeSpan = outerRange

-- defaults ok
instance GetRange ()
instance GetRange Char
instance GetRange Bool
instance GetRange Int
instance GetRange Integer
instance GetRange (Ratio a) -- for Rational

instance GetRange a => GetRange (Maybe a) where
    getRange = maybe nullRange getRange
    rangeSpan = maybe [] rangeSpan

instance GetRange a => GetRange [a] where
    getRange = concatMapRange getRange
    rangeSpan = joinRanges . map rangeSpan

instance (GetRange a, GetRange b) => GetRange (a, b) where
    getRange = getRange . fst
    rangeSpan (a, b) = sortRange (rangeSpan a) $ rangeSpan b

instance GetRange a => GetRange (Set.Set a) where
    getRange = getRange . Set.toList
    rangeSpan = rangeSpan . Set.toList

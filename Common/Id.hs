{- |
Module      :  $Header$
Description :  positions, simple and mixfix identifiers
Copyright   :  (c) Klaus Lüttich and Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

-- do use in data types that derive d directly
data Pos = SourcePos { sourceName :: String
                     , sourceLine :: !Int
                     , sourceColumn :: !Int } deriving (Eq, Ord)

instance Show Pos where
    showsPrec _ = showPos

-- | position lists with trivial equality
newtype Range = Range [Pos]

-- let InlineAxioms recognize positions
instance Show Range where
    show _ = "nullRange"

-- ignore all ranges in comparisons
instance Eq Range where
    _ == _ = True

-- Ord must be consistent with Eq
instance Ord Range where
   compare _ _ = EQ

rangeToList :: Range -> [Pos]
rangeToList (Range l) = l

nullRange :: Range
nullRange = Range []

isNullRange :: Range -> Bool
isNullRange (Range l) = null l

appRange :: Range -> Range -> Range
appRange (Range l1) (Range l2) = Range (l1++l2)

reverseRange :: Range -> Range
reverseRange (Range l) = Range (reverse l)

concatMapRange :: (a -> Range) -> [a] -> Range
concatMapRange f = Range . concatMap (rangeToList . f)

comparePos :: Pos -> Pos -> Ordering
comparePos = compare

-- | construct a new position
newPos :: String -> Int -> Int -> Pos
newPos = SourcePos

-- | increment the column counter
incSourceColumn :: Pos -> Int -> Pos
incSourceColumn (SourcePos s l c) i = SourcePos s l (c + i)

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
                   } deriving (Eq, Ord)

instance Show Token where
  show = tokStr

-- | simple ids are just tokens
type SIMPLE_ID = Token

-- | construct a token without position from a string
mkSimpleId :: String -> Token
mkSimpleId s = Token s nullRange

extSimpleId :: String -> SIMPLE_ID -> SIMPLE_ID
extSimpleId s sid = sid {tokStr = tokStr sid ++ s}

isSimpleToken :: Token -> Bool
isSimpleToken t = case tokStr t of
    c : r -> isAlpha c || isDigit c && null r || c == '\''
    "" -> False

-- | show the plain string
showTok :: Token -> ShowS
showTok = showString . tokStr

-- | collect positions
catPosAux :: [Token] -> [Pos]
catPosAux = concatMap (rangeToList . tokPos)

catPos :: [Token] -> Range
catPos = Range . catPosAux

-- | shortcut to get positions of surrounding and interspersed tokens
toPos :: Token -> [Token] -> Token -> Range
toPos o l c = catPos $ o:l++[c]

toPosAux :: Token -> [Token] -> Token -> [Pos]
toPosAux o l c = catPosAux $ o:l++[c]

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
equalS  = "="

-- | mind spacing i.e. in @e =e= e@
exEqual :: String
exEqual  = "=e="

-- | token for type annotations
typeTok :: Token
typeTok = mkSimpleId ":"

-- * identifiers with positions (usually ignored) of compound lists

-- | mixfix and compound identifiers
data Id = Id [Token] [Id] Range
          -- pos of square brackets and commas of a compound list
          --deriving Show

instance Show Id where
  showsPrec _ = showId

-- | construct an 'Id' from a token list
mkId :: [Token] -> Id
mkId toks = Id toks [] (Range [])

mkInfix :: String -> Id
mkInfix s = mkId [placeTok, mkSimpleId s, placeTok]

-- ignore positions
instance Eq Id where
    Id tops1 ids1 _ == Id tops2 ids2 _ = (tops1, ids1) == (tops2, ids2)

-- ignore positions
instance Ord Id where
    Id tops1 ids1 _ <= Id tops2 ids2 _ = (tops1, ids1) <= (tops2, ids2)

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
showSepList _ _ [] = id
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r

-- | shows a compound list
showIds :: [Id] -> ShowS
showIds is = noShow (null is) $ showString "["
             . showSepList (showString ",") showId is
             . showString "]"

-- | shows an 'Id', puts final places behind a compound list
showId :: Id -> ShowS
showId (Id ts is _) =
        let (toks, places) = splitMixToken ts
            showToks = showSepList id showTok
        in  showToks toks . showIds is . showToks places

-- ** splitting identifiers

-- | splits off the front and final places
splitMixToken :: [Token] -> ([Token],[Token])
splitMixToken [] = ([], [])
splitMixToken (h:l) =
    let (toks, pls) = splitMixToken l
        in if isPlace h && null toks
           then (toks, h:pls)
           else (h:toks, pls)

-- | return open and closing list bracket and a compound list
-- from a bracket 'Id'  (parsed by 'Common.Anno_Parser.caslListBrackets')
getListBrackets :: Id -> ([Token], [Token], [Id])
getListBrackets (Id b cs _) =
    let (b1, rest) = break isPlace b
        b2 = if null rest then []
             else filter (not . isPlace) rest
    in (b1, b2, cs)

-- ** reconstructing token lists

-- | reconstruct a list with surrounding strings and interspersed commas
-- with proper position information
-- that should be preserved by the input function
expandPos :: (Token -> a) -> (String, String) -> [a] -> Range -> [a]
-- expandPos f ("{", "}") [a,b] [(1,1), (1,3), 1,5)] =
-- [ t"{" , a , t"," , b , t"}" ] where t = f . Token (and proper positions)
expandPos f (o, c) ts (Range ps) =
    if null ts then if null ps then map (f . mkSimpleId) [o, c]
       else map f (zipWith Token [o, c] [Range [head ps] , Range [last ps]])
    else  let n = length ts + 1
              diff = n - length ps
              commas j = if j == 2 then [c] else "," : commas (j - 1)
              ocs = o : commas n
              seps = map f (if diff == 0 then
                            zipWith ( \ s p -> Token s (Range [p]))
                            ocs ps else map mkSimpleId ocs)
          in head seps : concat (zipWith (\ t s -> [t,s]) ts (tail seps))

-- | reconstruct the token list of an 'Id'
-- including square brackets and commas of (nested) compound lists.
getPlainTokenList :: Id -> [Token]
getPlainTokenList (Id ts cs ps) =
    if null cs then ts else
       let (toks, pls) = splitMixToken ts in
           toks ++ getCompoundTokenList cs ps ++ pls

-- | reconstruct tokens of compound list
getCompoundTokenList :: [Id] -> Range -> [Token]
getCompoundTokenList cs ps = concat $ expandPos (:[]) ("[", "]")
              -- although positions will be replaced (by scan)
                             (map getPlainTokenList cs) ps

-- | reconstruct the token list of an 'Id'.
-- Replace top-level places with the input String
getTokenList :: String -> Id -> [Token]
getTokenList placeStr (Id ts cs ps) =
    let convert =  map (\ t -> if isPlace t then t {tokStr = placeStr} else t)
    in if null cs then convert ts else
       let (toks, pls) = splitMixToken ts in
           convert toks ++ getCompoundTokenList cs ps ++ convert pls

-- ** conversion from 'SIMPLE_ID'

-- | a 'SIMPLE_ID' as 'Id'
simpleIdToId :: SIMPLE_ID -> Id
simpleIdToId sid = Id [sid] [] (Range [])

-- | a string as 'Id'
stringToId :: String -> Id
stringToId sid = simpleIdToId $ mkSimpleId sid

-- | efficiently test for a singleton list
isSingle :: [a] -> Bool
isSingle [_] = True
isSingle _   = False

-- | test for a 'SIMPLE_ID'
isSimpleId :: Id -> Bool
isSimpleId (Id ts cs _) = null cs && case ts of
    [t] -> isSimpleToken t
    _ -> False

-- ** fixity stuff

-- | number of 'place' in 'Id'
placeCount :: Id -> Int
placeCount (Id tops _ _) = length $ filter isPlace tops

-- | has no (toplevel) 'place'
isOrdAppl :: Id -> Bool
isOrdAppl = not . isMixfix

-- | has a 'place'
isMixfix :: Id -> Bool
isMixfix (Id tops _ _) = any isPlace tops

-- | 'Id' starts with a 'place'
begPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)

-- | 'Id' ends with a 'place'
endPlace :: Id -> Bool
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

-- | ends with a 'place'
isPrefix :: Id -> Bool
isPrefix (Id tops _ _) = not (null tops) && not (isPlace (head tops))
                         && isPlace (last tops)

-- | starts with a 'place'
isPostfix :: Id -> Bool
isPostfix (Id tops _ _) = not (null tops) &&  isPlace (head  tops)
                          && not (isPlace (last tops))

-- | is a classical infix 'Id' with three tokens,
-- the middle one is a non-'place'
isInfix2 :: Id -> Bool
isInfix2 (Id ts _ _) =
    case ts of
            [e1, e2, e3] -> isPlace e1 && not (isPlace e2)
                            && isPlace e3
            _ -> False

-- | starts and ends with a 'place'
isInfix :: Id -> Bool
isInfix (Id tops _ _) = not (null tops) &&  isPlace (head tops)
                        && isPlace (last tops)

-- | has a 'place' but neither starts nor ends with one
isSurround :: Id -> Bool
isSurround i@(Id tops _ _) = not (null tops) && (isMixfix i)
                             && not (isPlace (head tops))
                                    && not (isPlace (last tops))

-- * position stuff

-- | compute a meaningful single position from an 'Id' for diagnostics
posOfId :: Id -> Range
posOfId (Id ts _ (Range ps)) =
   Range $ let l = filter (not . isPlace) ts
                       in (if null l then
                       -- for invisible "__ __" (only places)
                          catPosAux ts
                          else catPosAux l) ++ ps

-- | get a reasonable position for a list
posOf :: PosItem a => [a] -> Range
posOf = Range . concatMap getPosList


-- | get a reasonable position for a list with an additional position list
firstPos :: PosItem a => [a] -> Range -> Range
firstPos l (Range ps) = Range (rangeToList (posOf l) ++ ps)

---- helper class -------------------------------------------------------

{- | This class is derivable with DrIFT.
   Its main purpose is to have a function that operates on
   constructors with a 'Pos' or list of 'Pos' field. During parsing, mixfix
   analysis and ATermConversion this function might be very useful.
-}

class PosItem a where
    getRange :: a -> Range
    getRange _ = nullRange  -- default implementation

getPosList :: PosItem a => a -> [Pos]
getPosList = rangeToList . getRange

-- handcoded instance
instance PosItem Token where
    getRange (Token _ p) = p

-- handcoded instance
instance PosItem Id where
    getRange = posOfId

-- handcoded instance
instance PosItem ()
    -- default is ok

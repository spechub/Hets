{- |
Module      :  $Header$
Description :  generic mixfix analysis, using an Earley parser
Copyright   :  Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Generic mixfix analysis, using an Earley parser

The grammer has a single non-terminal for terms (the double
underscore). A rule of the grammer carries an identifier, a precedence
number, and the actual token list of the identifier to match against
the input token list..

The parser can be instantiated for any term type. A
function parameter determines how applications from identifiers and
arguments are constructed.
-}

module Common.Earley
    ( Rule
    , Rules
    , partitionRules
    -- * special tokens for special ids
    , varTok
    , exprTok
    , parenId
    , exprId
    , varId
    , tupleId
    , unitId
    , protect
    , listRules
    , mixRule
    , getTokenPlaceList
    , getPlainPolyTokenList
    , getPolyTokenList
    -- * resolution chart
    , Chart
    , mixDiags
    , solveDiags
    , ToExpr
    , rules
    , addRules
    , initChart
    , nextChart
    , getResolved
    ) where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Prec
import Common.Result
import Common.Utils (nubOrd)

import Control.Exception

import Data.List
import Data.Maybe
import qualified Data.Map as Map

-- | take the difference of the two input lists take (length l2 - length l1) l2
takeDiff :: [a] -> [b] -> [b]
takeDiff l1 l2 = zipWith const l2 $ dropPrefix l1 l2

-- | update token positions.
-- return remaining positions
setToksPos :: [Token] -> Range -> ([Token], Range)
setToksPos (h : ts) (Range (p : ps)) =
    let (rt, rp) = setToksPos ts (Range ps)
        in (h {tokPos = Range $ if isPlace h then [p, p] else [p]} : rt, rp)
setToksPos ts ps = (ts, ps)

reverseRange :: Range -> Range
reverseRange = Range . reverse . rangeToList

-- | update positions in 'Id'.
-- return remaining positions
setPlainIdePos :: Id -> Range -> (Id, Range)
setPlainIdePos (Id ts cs _) ps =
    if null cs then
       let (newTs, restPs) = setToksPos ts ps
           in (Id newTs cs nullRange, restPs)
    else let (toks, pls) = splitMixToken ts
             (front, ps2) = setToksPos toks ps
             ps2PL = rangeToList ps2
             (newCs, ps3, ps4) =
                 if isNullRange ps2 then error "setPlainIdePos2"
                    else foldl ( \ (prevCs, seps, restPs) a ->
                         let (c1, qs) = setPlainIdePos a restPs
                             qsPL = rangeToList qs
                         in if isNullRange qs then error "setPlainIdePos1"
                            else (c1: prevCs,
                                  Range (head qsPL : rangeToList seps),
                                  Range (tail qsPL)))
                           ([], Range [head ps2PL], Range (tail ps2PL)) cs
             (newPls, ps7) = setToksPos pls ps4
           in (Id (front ++ newPls) (reverse newCs) (reverseRange ps3), ps7)

-- no special index type anymore (assuming not much more development)
-- the info Int denotes fast precedence

data Item a = Item
    { rule :: Id        -- the rule to match
    , info :: Int       -- additional precedence info for 'rule'
    , lWeight :: Id     -- weights for lower precedence pre- and postfixes
    , rWeight :: Id     -- given by the 'Id's itself
    , posList :: Range  -- positions of Id tokens
    , args :: [a]       -- currently collected arguments
      -- both in reverse order
    , ambigArgs :: [[a]] -- field for ambiguities
    , ambigs :: [[a]]   -- field for ambiguities
    , rest :: [Token]   -- part of the rule after the "dot"
    , index :: Int    -- index into the Table/input string
    }

-- | the non-terminal
termStr :: String
termStr = "(__)"
-- | builtin terminals
commaTok, termTok, oParenTok, cParenTok :: Token
commaTok = mkSimpleId "," -- for list elements
termTok = mkSimpleId termStr
oParenTok = mkSimpleId "("
cParenTok = mkSimpleId ")"
listTok :: Token
listTok = mkSimpleId "[]" -- impossible token
protectTok :: Token
protectTok = mkSimpleId "()" -- impossible token

-- | token for a fixed (or recursively resolved) operator expression
exprTok :: Token
exprTok = mkSimpleId "(op )"

-- | token for a fixed (or recursively resolved) argument expression
varTok :: Token
varTok = mkSimpleId "(var )"

-- | parenthesis around one place
parenId :: Id
parenId = mkId [oParenTok, placeTok, cParenTok]

-- | id for tuples with at least two arguments
tupleId :: Id
tupleId = mkId [oParenTok, placeTok, commaTok, placeTok, cParenTok]

-- | id for the emtpy tuple
unitId :: Id
unitId = mkId [oParenTok, cParenTok]

-- | see 'exprTok'
exprId :: Id
exprId = mkId [exprTok]

-- | see 'varTok'
varId :: Id
varId = mkId [varTok]

listId :: (Id, Id) -> Id
listId (f,c) = Id [listTok] [f,c] nullRange

isListId :: Id -> Bool
isListId (Id ts _ _) = not (null ts) && head ts == listTok

-- | interpret placeholders as literal places
protect :: Id -> Id
protect i = Id [protectTok] [i] nullRange

unProtect :: Id -> Maybe Id
unProtect (Id ts cs _) = case cs of
    [i] -> case ts of
      [tok] | tok == protectTok -> Just i
      _ -> Nothing
    _ -> Nothing

-- | get the token list for a mixfix rule
getPolyTokenList :: Id -> [Token]
getPolyTokenList = getGenPolyTokenList termStr

-- | get the plain token list for prefix applications
getPlainPolyTokenList :: Id -> [Token]
getPlainPolyTokenList = getGenPolyTokenList place

type Rule = (Id, Int, [Token])

mkItem :: Int -> Rule -> Item a
mkItem ind (ide, inf, toks) = Item
   { rule = ide
   , info = inf
   , lWeight = ide
   , rWeight = ide
   , posList = nullRange
   , args = []
   , ambigArgs = []
   , ambigs = []
   , rest = toks
   , index = ind }

-- | extract tokens with the non-terminal for places
getTokenPlaceList :: Id -> [Token]
getTokenPlaceList = getTokenList termStr

-- | construct a rule for a mixfix
mixRule :: Int -> Id -> Rule
mixRule b i = (i, b, getTokenPlaceList i)

asListAppl :: ToExpr a -> Id -> [a] -> Range -> a
asListAppl toExpr i ra br
  | isListId i =
      let Id _ [f, c] _ = i
          mkList [] ps = toExpr c [] ps
          mkList (hd:tl) ps = toExpr f [hd, mkList tl ps] ps
      in mkList ra br
  | elem i [typeId, exprId, parenId, varId] = case ra of
         [arg] -> arg
         _ -> error "asListAppl"
  | otherwise = toExpr i ra br

-- | construct the list rules
listRules :: Int -> GlobalAnnos -> [Rule]
listRules inf g =
    let lists = list_lit $ literal_annos g
        listRule co toks = (listId co, inf, toks)
    in concatMap ( \ (bs, (n, c)) ->
       let (b1, b2, cs) = getListBrackets bs
           e = Id (b1 ++ b2) cs nullRange in
           (if e == n then [] -- add b1 ++ b2 if its not yet included by n
               else [listRule (c, n) $ getPlainTokenList e])
           ++ [listRule (c, n) (b1 ++ [termTok] ++ b2),
               listRule (c, n) (b1 ++ [termTok, commaTok, termTok] ++ b2)]
                 ) $ Map.toList lists

type Table a = Map.Map Int [Item a]

lookUp :: Table a -> Int -> [Item a]
lookUp ce k = Map.findWithDefault [] k ce

-- | recognize next token (possible introduce new tuple variable)
scanItem :: (a -> a -> a) -> (a, Token) -> Item a -> [Item a]
scanItem addType (trm, t)
  p@Item{ rest = ts, args = pArgs, posList = pRange } = case ts of
       [] -> []
       hd : tt -> let
          q = p { posList = case rangeToList $ tokPos t of
                [] -> pRange
                ps@(po : _) -> Range $ (if null tt then last ps else po)
                   : rangeToList pRange }
          r = q { rest = tt } in
          if hd == t || t == exprTok && hd == varTok then
               if t == commaTok then
                  case tt of
                  sd : _ | sd == termTok ->
                      -- tuple or list elements separator
                             [ r, q { rest = termTok : ts } ]
                  _ -> [r]
              else if elem t [exprTok, varTok, typeInstTok] then
                   [r { args = trm : pArgs }]
              else if t == typeTok then
                  case (tt, pArgs) of
                  ([], [arg]) -> [q { rest = [], args = [addType trm arg] }]
                  _ -> error "scanItem: typeTok"
              else [r]
          else []

scan :: (a -> a -> a) -> (a, Token) -> [Item a] -> [Item a]
scan f = concatMap . scanItem f

mkAmbigs :: ToExpr a -> Item a -> [a]
mkAmbigs toExpr p@Item{ args = l, ambigArgs = aArgs } =
    map ( \ aas -> fst $
          mkExpr toExpr
          p { args = takeDiff aas l ++ aas
            } ) aArgs

addArg :: GlobalAnnos -> ToExpr a -> Item a -> Item a -> Item a
addArg ga toExpr argItem@Item { ambigs = ams, posList = aRange }
  p@Item{ args = pArgs, rule = op, posList = pRange, ambigs = pAmbs
        , rest = pRest} =
    let (arg, _) = mkExpr toExpr argItem
        newAms = mkAmbigs toExpr argItem
        q = case pRest of
            _ : tl ->
               p { rest = tl
                 , posList = case rangeToList aRange of
                     [] -> pRange
                     qs@(h : _) -> Range $ (if null tl then
                        last qs else h) : rangeToList pRange
                 , args = arg : pArgs
                 , ambigs = (if null newAms then ams else newAms : ams)
                            ++ pAmbs }
            _ -> error "addArg"
        in if isLeftArg op pArgs then
              q { lWeight = getNewWeight ALeft ga argItem op }
           else if isRightArg op pArgs then
                q { rWeight = getNewWeight ARight ga argItem op }
           else q

-- | shortcut for a function that constructs an expression
type ToExpr a = Id -> [a] -> Range -> a

mkExpr :: ToExpr a -> Item a -> (a, Range)
mkExpr toExpr Item { rule = orig, posList = ps, args = iArgs } =
    let rs = reverseRange ps
        (ide, qs) = if isListId orig then (orig, rs) else
                    setPlainIdePos (fromMaybe orig $ unProtect orig) rs
        in (asListAppl toExpr ide (reverse iArgs) qs, rs)

reduce :: GlobalAnnos -> Table a -> ToExpr a -> Item a -> [Item a]
reduce ga table toExpr itm =
    map (addArg ga toExpr itm)
        $ filter (checkPrecs ga itm)
        $ lookUp table $ index itm

getWeight :: AssocEither -> Item a -> Id
getWeight side = case side of
    ALeft -> lWeight
    ARight -> rWeight

getNewWeight :: AssocEither -> GlobalAnnos -> Item a -> Id -> Id
getNewWeight side ga = nextWeight side ga . getWeight side

-- | check precedences of an argument and a top-level operator.
checkPrecs :: GlobalAnnos -> Item a -> Item a -> Bool
checkPrecs ga argItem@Item { rule = arg, info = argPrec }
              Item { rule = op, info = opPrec, args = oArgs } =
    checkPrec ga (op, opPrec) (arg, argPrec) oArgs $ flip getWeight argItem

reduceCompleted :: GlobalAnnos -> Table a -> ToExpr a -> [Item a] -> [Item a]
reduceCompleted ga table toExpr =
    foldr mergeItems [] . map (reduce ga table toExpr) .
          filter (null . rest)

recReduce :: GlobalAnnos -> Table a -> ToExpr a -> [Item a] -> [Item a]
recReduce ga table toExpr items =
    let reduced = reduceCompleted ga table toExpr items
        in if null reduced then items
           else recReduce ga table toExpr reduced `mergeItems` items

complete :: ToExpr a -> GlobalAnnos -> Table a -> [Item a] -> [Item a]
complete toExpr ga table items =
    let reducedItems = recReduce ga table toExpr $
                       reduceCompleted ga table toExpr items
        in reducedItems ++ items

doPredict :: [Item a] -> ([Item a], [Item a])
doPredict = partition ( \ Item{ rest = ts } ->
                      not (null ts) && head ts == termTok)

ordItem :: Item a -> Item a -> Ordering
ordItem Item{ index = i1, rest = r1, rule = n1 }
    Item{ index = i2, rest = r2, rule = n2 } =
    compare (i1, r1, n1) (i2, r2, n2)

ambigItems :: Item a -> Item a -> Item a
ambigItems i1@Item{ ambigArgs = ams1, args = as1 }
    Item{ ambigArgs = ams2, args = as2 } =
    i1 { ambigArgs = case ams1 ++ ams2 of
         [] -> [as1, as2]
         ams -> ams }

mergeItems :: [Item a] -> [Item a] -> [Item a]
mergeItems [] i2 = i2
mergeItems i1 [] = i1
mergeItems (i1:r1) (i2:r2) =
    case ordItem i1 i2 of
    LT -> i1 : mergeItems r1 (i2:r2)
    EQ -> ambigItems i1 i2 : mergeItems r1 r2
    GT -> i2 : mergeItems (i1:r1) r2

-- | the whole state for mixfix resolution
data Chart a = Chart
    { prevTable :: Table a
    , currIndex :: Int
    , currItems :: ([Item a], [Item a])
    , rules :: ([Rule], [Rule])
    , addRules :: Token -> [Rule]
    , solveDiags :: [Diagnosis] }

-- | make one scan, complete, and predict step.
-- The first function adds a type to the result.
-- The second function filters based on argument and operator info.
-- If filtering yields 'Nothing' further filtering by precedence is applied.
nextChart :: (a -> a -> a) -> ToExpr a -> GlobalAnnos
          -> Chart a -> (a, Token) -> Chart a
nextChart addType toExpr ga st term@(_, tok) = let
    table = prevTable st
    idx = currIndex st
    igz = idx > 0
    (cItems, sItems) = currItems st
    (cRules, sRules) = rules st
    pItems = if null cItems && igz then sItems else
        map (mkItem idx) (addRules st tok ++ sRules) ++ sItems
    scannedItems = scan addType term pItems
    nextTable = if null cItems && igz then table else
        Map.insert idx (map (mkItem idx) cRules ++ cItems) table
    completedItems = complete toExpr ga nextTable $ sortBy ordItem scannedItems
    nextIdx = idx + 1
    in if null pItems && igz then st else st
    { prevTable = nextTable
    , currIndex = nextIdx
    , currItems = doPredict completedItems
    , solveDiags =
        [ Diag Error ("unexpected mixfix token: " ++ tokStr tok) $ tokPos tok
        | null scannedItems ] ++ solveDiags st }

-- | add intermediate diagnostic messages
mixDiags :: [Diagnosis] -> Chart a -> Chart a
mixDiags ds st = st { solveDiags = ds ++ solveDiags st }

type Rules = ([Rule], [Rule]) -- postfix and prefix rules

-- | presort rules
partitionRules :: [Rule] -> Rules
partitionRules = partition ( \ (_, _, t : _) -> t == termTok)

-- | create the initial chart
initChart :: (Token -> [Rule]) -> Rules -> Chart a
initChart adder ruleS = Chart
    { prevTable = Map.empty
    , currIndex = 0
    , currItems = ([], [])
    , rules = ruleS
    , addRules = adder
    , solveDiags = [] }

-- | extract resolved result
getResolved :: (a -> ShowS) -> Range -> ToExpr a -> Chart a -> Result a
getResolved pp p toExpr st = let
   (predicted, items') = currItems st
   ds = solveDiags st
   items = if null items' && null ds then predicted else items'
   in case items of
   [] -> assert (not $ null ds) $ Result ds Nothing
   _ -> let
     (finals, r1) = partition ((0 ==) . index) items
     (result, r2) = partition (null . rest) finals
     in case result of
     [] -> let
       expected = if null r2 then filter (not . null . rest) r1 else r2
       withpos = filter (not . isNullRange . posList) expected
       (q, errs) = if null withpos then (p, expected) else
         (concatMapRange (reverseRange . posList) withpos, withpos)
       in Result (Diag Error ("expected further mixfix token: "
          ++ show (take 5 $ nubOrd $ map (tokStr . head . rest) errs)) q : ds)
          Nothing
     [har] -> case ambigs har of
       [] -> case mkAmbigs toExpr har of
         [] -> Result ds $ Just $ fst $ mkExpr toExpr har
         ambAs -> Result (showAmbigs pp p (take 5 ambAs) : ds) Nothing
       ams -> Result (map (showAmbigs pp p) (take 5 ams) ++ ds) Nothing
     _ -> Result (showAmbigs pp p (map (fst . mkExpr toExpr) result) : ds)
       Nothing

showAmbigs :: (a -> ShowS) -> Range -> [a] -> Diagnosis
showAmbigs pp p as = Diag Error
    ("ambiguous mixfix term\n  " ++ showSepList (showString "\n  ") pp
     (take 5 as) "") p

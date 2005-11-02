{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

generic mixfix analysis
-}

module Common.Earley (Rule
                     -- * special tokens for special ids
                     , varTok, exprTok, typeTok
                     , applId, parenId, typeId, exprId, varId
                     , tupleId, unitId, unknownId, isUnknownId, unToken
                     , Knowns, protect, listRules, mixRule
                     , getTokenPlaceList
                     , endPlace, begPlace
                     -- * resolution chart
                     , Chart, mixDiags, ToExpr
                     , initChart, nextChart, getResolved
                     -- * printing
                     , joinPlace, isLeftArg, isRightArg)
    where

import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Data.List

-- | drop as many elements as are in the first list
dropPrefix :: [a] -> [b] -> [b]
dropPrefix [] l = l
dropPrefix _ [] = []
dropPrefix (_ : xs) (_ : ys) = dropPrefix xs ys

-- | take the difference of the two input lists take (length l2 - length l1) l2
takeDiff :: [a] -> [b] -> [b]
takeDiff l1 l2 = zipWith const l2 $ dropPrefix l1 l2

-- | reconstruct the token list of an 'Id'.
-- Replace top-level places with the input String
getTokenList :: String -> Id -> [Token]
getTokenList placeStr (Id ts cs ps) =
    let convert =  map (\ t -> if isPlace t then t {tokStr = placeStr} else t)
    in if null cs then convert ts else
       let (toks, pls) = splitMixToken ts in
           convert toks ++ getCompoundTokenList cs ps ++ convert pls

-- | update token positions.
-- return remaining positions
setToksPos :: [Token] -> Range -> ([Token], Range)
setToksPos (h:ts) (Range (p:ps)) =
    let (rt, rp) = setToksPos ts (Range ps)
        in (h {tokPos = Range [p]} : rt, rp)
setToksPos ts ps = (ts, ps)

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

-- | a special index type for more type safety
newtype Index = Index Int deriving (Eq, Ord, Show)

-- deriving Num is also possible
-- but the following functions are sufficient
-- | the initial index
startIndex :: Index
startIndex = Index 0

incrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)

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
    , index :: Index    -- index into the Table/input string
    }

instance Show (Item a) where
    showsPrec _ Item { rule = ide, rest = d, index = Index i } =
        let v = getPlainTokenList ide
            first = takeDiff d v
            showToks = showSepList id showTok
            in showChar '['. showToks first
                          . showChar '.'
                          . showToks d
                          . showString ", "
                          . shows i . showChar ']'

-- | the non-terminal
termStr :: String
termStr = "(__)"
-- | builtin terminals
commaTok, termTok, oParenTok, cParenTok, placeTok :: Token
commaTok = mkSimpleId "," -- for list elements
termTok = mkSimpleId termStr
placeTok = mkSimpleId place
oParenTok = mkSimpleId "("
cParenTok = mkSimpleId ")"
listTok :: Token
listTok = mkSimpleId "[]" -- impossible token
protectTok :: Token
protectTok = mkSimpleId "()" -- impossible token

-- | token for type annotations
typeTok :: Token
typeTok = mkSimpleId ":"

-- | token for a fixed (or recursively resolved) operator expression
exprTok :: Token
exprTok = mkSimpleId "(op )"
-- | token for a fixed (or recursively resolved) argument expression
varTok :: Token
varTok = mkSimpleId "(var )"
-- | token for an unknown variable (within patterns)
unknownTok :: Token
unknownTok = mkSimpleId "(?)"

-- | the invisible application rule with two places
applId :: Id
applId = mkId [placeTok, placeTok]
-- | parenthesis around one place
parenId :: Id
parenId = mkId [oParenTok, placeTok, cParenTok]
-- | id for tuples with at least two arguments
tupleId :: Id
tupleId = mkId [oParenTok, placeTok, commaTok, placeTok, cParenTok]
-- | id for the emtpy tuple
unitId :: Id
unitId = mkId [oParenTok, cParenTok]
-- | see 'typeTok'
typeId :: Id
typeId = mkId [placeTok, typeTok]
-- | see 'exprTok'
exprId :: Id
exprId = mkId [exprTok]
-- | see 'varTok'
varId :: Id
varId = mkId [varTok]
-- | see 'unknownTok'
unknownId :: Id
unknownId = mkId [unknownTok]

listId :: (Id, Id) -> Id
listId (f,c) = Id [listTok] [f,c] nullRange

isListId :: Id -> Bool
isListId (Id ts _ _) = not (null ts) && head ts == listTok

-- | interpret placeholders as literal places
protect :: Id -> Id
protect i = Id [protectTok] [i] nullRange

unProtect :: Id -> Id
unProtect (Id _ [i] _) = i
unProtect _ = error "unProtect"

isProtected :: Id -> Bool
isProtected (Id ts _ _) = not (null ts) && head ts == protectTok

-- | test if an 'unknownId' was matched
isUnknownId :: Id -> Bool
isUnknownId (Id ts _ _) = not (null ts) && head ts == unknownTok

-- | get unknown token from an 'unknownId'
unToken :: Id -> Token
unToken (Id [_,t] _ _) = t
unToken _ = error "unToken"

type Rule = (Id, Int, [Token])

mkItem :: Index -> Rule -> Item a
mkItem ind (ide, inf, toks) =
    Item { rule = ide
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
asListAppl toExpr i ra br =
    if isListId i then
           let Id _ [f, c] _ = i
               mkList [] ps = toExpr c [] ps
               mkList (hd:tl) ps = toExpr f [hd, mkList tl ps] ps
           in mkList ra br
    else if i == typeId
             || i == exprId
             || i == parenId
             || i == varId
             then case ra of
                  [arg] -> arg
                  _ -> error "asListAppl"
    else toExpr i ra br

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

type Table a = Map.Map Index [Item a]

lookUp :: Table a -> Index -> [Item a]
lookUp ce k = Map.findWithDefault [] k ce

-- | a set of strings that do not match a 'unknownTok'
type Knowns = Set.Set String

-- | recognize next token (possible introduce new tuple variable)
scanItem :: (a -> a -> a) -> Knowns -> (a, Token) -> Item a -> [Item a]
scanItem addType ks (trm, t)
    p@Item{ rest = ts, args = pArgs, rule = ide, posList = pRange } =
    let q = p { posList = tokPos t `appRange` pRange }
    in case ts of
       [] -> []
       hd : tt -> let r = q { rest = tt } in
          if hd == t || t == exprTok && hd == varTok then
               if t == commaTok then
                  case tt of
                  sd : _ | sd == termTok ->
                      -- tuple or list elements separator
                             [ r, q { rest = termTok : ts } ]
                  _ -> [r]
              else if t == exprTok || t == varTok then
                   [r { args = trm : pArgs }]
              else if t == typeTok then
                  case (tt, pArgs) of
                  ([], [arg]) -> [q { rest = [], args = [addType trm arg] }]
                  _ -> error "scanItem: typeTok"
              else [r]
          else if Set.null ks then []
               else if isUnknownId ide
                 && not (tokStr t `Set.member` ks) then
               [r { rule = mkId [unknownTok, t]}]
               else []

scan :: (a -> a -> a) -> Knowns -> (a, Token) -> [Item a] -> [Item a]
scan f ks term = concatMap (scanItem f ks term)

mkAmbigs :: ToExpr a -> Item a -> [a]
mkAmbigs toExpr p@Item{ args = l, ambigArgs = aArgs } =
    map ( \ aas -> fst $
          mkExpr toExpr
          p { args = takeDiff aas l ++ aas
            } ) aArgs

addArg :: GlobalAnnos -> ToExpr a -> Item a -> Item a -> Item a
addArg ga toExpr argItem@Item { ambigs = ams } p@Item{ args = pArgs,
    rule = op, posList = pRange, ambigs = pAmbs, rest = pRest} =
    let (arg, ps) = mkExpr toExpr argItem
        newAms = mkAmbigs toExpr argItem
        q = case pRest of
            _ : tl ->
               p { rest = tl
                 , posList = ps `appRange` pRange
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
                     if isProtected orig then
                       setPlainIdePos (unProtect orig) rs
                    else setPlainIdePos orig rs
        in (asListAppl toExpr ide (reverse iArgs) qs, rs)

reduce :: GlobalAnnos -> Table a -> ToExpr a -> Item a -> [Item a]
reduce ga table toExpr itm =
    map (addArg ga toExpr itm)
        $ filter ( \ oi@Item{ rest = ts } -> case ts of
                   hd : _ | hd == termTok -> checkPrecs ga itm oi
                   _ -> False)
        $ lookUp table $ index itm

-- | 'Id' starts with a 'place'
begPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)

-- | 'Id' ends with a 'place'
endPlace :: Id -> Bool
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

-- | check if a left argument will be added.
-- (The 'Int' is the number of current arguments.)
isLeftArg :: Id -> [a] -> Bool
isLeftArg op nArgs = null nArgs && begPlace op
-- | check if a right argument will be added.
isRightArg :: Id -> [a] -> Bool
isRightArg op@(Id toks _ _) nArgs = endPlace op &&
    (isSingle $ dropPrefix nArgs $ filter isPlace toks)

getWeight :: AssocEither -> Item a -> Id
getWeight side = case side of
    ALeft -> lWeight
    ARight -> rWeight

joinPlace :: AssocEither -> Id -> Bool
joinPlace side = case side of
    ALeft -> begPlace
    ARight -> endPlace

getNewWeight :: AssocEither -> GlobalAnnos -> Item a -> Id -> Id
getNewWeight side ga argItem op =
    let arg = getWeight side argItem
    in if joinPlace side arg then
          case precRel (prec_annos ga) op arg of
            Higher -> arg
            _ -> op
       else op

checkArg :: AssocEither -> GlobalAnnos -> Item a -> Item a -> Bool
checkArg side ga argItem@Item{ rule = arg, info = argPrec }
         Item{ rule = op, info = opPrec } =
    let precs = prec_annos ga
        assocs = assoc_annos ga
        weight = getWeight side argItem
    in if argPrec <= 0 then False
       else case compare argPrec opPrec of
           LT -> False
           GT -> True
           EQ -> if joinPlace side arg then
               case precRel precs op weight of
               Lower -> True
               Higher -> False
               BothDirections -> False
               NoDirection ->
                   case (isInfix arg, joinPlace side op) of
                        (True, True) -> if arg == op
                                        then not $ isAssoc side assocs op
                                        else True
                        (False, True) -> True
                        (True, False) -> False
                        _ -> side == ALeft
            else True

-- | check precedences of an argument and a top-level operator.
-- (The 'Int' is the number of current arguments of the operator.)
checkPrecs :: GlobalAnnos -> Item a -> Item a -> Bool
checkPrecs ga argItem opItem@Item{ rule = op, args = oArgs } =
    if isLeftArg op oArgs then checkArg ARight ga argItem opItem
    else if isRightArg op oArgs then checkArg ALeft ga argItem opItem
    else True

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
        in reducedItems
           ++ items

predict :: [Item a] -> [Item a] -> [Item a]
predict rs items =
    if any ( \ Item{ rest = ts } ->
            not (null ts) && head ts == termTok) items
    then rs ++ items
    else items

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
data Chart a = Chart { prevTable :: Table a
                       , currIndex :: Index
                       , currItems :: [Item a]
                       , rules :: [Rule]
                       , knowns :: Knowns
                       , solveDiags :: [Diagnosis] }
               deriving Show

-- | make one scan, complete, and predict step.
-- The first function adds a type to the result.
-- The second function filters based on argument and operator info.
-- If filtering yields 'Nothing' further filtering by precedence is applied.
nextChart :: (a -> a -> a) -> ToExpr a -> GlobalAnnos -> Chart a
          -> (a, Token) -> Chart a
nextChart addType toExpr ga st term@(_, tok) =
    let table = prevTable st
        idx = currIndex st
        items = currItems st
        rs = rules st
        scannedItems = scan addType (knowns st) term items
        nextTable = Map.insert idx items table
        nextIdx = incrIndex idx
    in  if null items then st else
        st { prevTable = nextTable
           , currIndex = nextIdx
           , currItems =  predict (map (mkItem nextIdx) rs)
           $ complete toExpr ga nextTable
           $ sortBy ordItem scannedItems
           , solveDiags = (if null scannedItems then
                      [Diag Error ("unexpected mixfix token: " ++ tokStr tok)
                      $ tokPos tok]
                      else []) ++ solveDiags st }

-- | add intermediate diagnostic messages
mixDiags :: [Diagnosis] -> Chart a -> Chart a
mixDiags ds st = st { solveDiags = ds ++ solveDiags st }

-- | create the initial chart
initChart :: [Rule] -> Knowns -> Chart a
initChart ruleS knownS =
    Chart { prevTable = Map.empty
          , currIndex = startIndex
          , currItems = map (mkItem startIndex) ruleS
          , rules = ruleS
          , knowns = knownS
          , solveDiags = [] }

-- | extract resolved result
getResolved :: (a -> ShowS) -> Range -> ToExpr a -> Chart a -> Result a
getResolved pp p toExpr st =
    let items = filter ((currIndex st/=) . index) $ currItems st
        ds = solveDiags st
    in case items of
       [] -> Result ds Nothing
       _ -> let (finals, rest1) = partition ((startIndex==) . index) items
                (result, rest2) = partition (null . rest) finals
            in case result of
               [] ->      let expected = if null rest2
                                         then filter (not . null . rest) rest1
                                         else rest2
                              withpos = filter (not . isNullRange . posList)
                                        expected
                              (q, errs) = if null withpos then (p, expected)
                                            else (concatMapRange
                                                  (reverseRange . posList)
                                                  withpos, withpos)
                              in Result (Diag Error
                               ("expected further mixfix token: "
                                ++ show (take 5 $ nub
                                        $ map (tokStr . head . rest)
                                         errs)) q : ds) Nothing
               [har] -> case ambigs har of
                   [] -> case mkAmbigs toExpr har of
                         [] -> Result ds $ Just $ fst $ mkExpr toExpr har
                         ambAs -> Result ((showAmbigs pp p $
                                             take 5 ambAs) : ds) Nothing
                   ams -> Result ((map (showAmbigs pp p) $
                                             take 5 ams) ++ ds) Nothing
               _ ->  Result ((showAmbigs pp p $
                            map (fst . mkExpr toExpr) result) : ds) Nothing

showAmbigs :: (a -> ShowS) -> Range -> [a] -> Diagnosis
showAmbigs pp p as =
    Diag Error ("ambiguous mixfix term\n  " ++
                showSepList (showString "\n  ") pp
                (take 5 as) "") p

{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2003 
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
                     , initChart, nextChart, getResolved)
    where

import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Data.List
import Control.Exception (assert)

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
             (newCs, ps3, ps4) = if isNullRange ps2 then error "setPlainIdePos2"
                                 else foldl ( \ (prevCs, seps, restPs) a -> 
                                  let (c1, qs) = setPlainIdePos a restPs
                                      qsPL = rangeToList qs
                                  in if isNullRange qs then error "setPlainIdePos1"
                                  else (c1: prevCs, Range (head qsPL : rangeToList seps), Range (tail qsPL)))
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
    showsPrec _ p = 
        let d = rest p
            v = getPlainTokenList (rule p)
            first = take (length v - length d) v
            showToks = showSepList id showTok
            Index i = index p 
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
applId       = mkId [placeTok, placeTok]
-- | parenthesis around one place
parenId :: Id
parenId      = mkId [oParenTok, placeTok, cParenTok]
-- | id for tuples with at least two arguments
tupleId :: Id
tupleId      = mkId [oParenTok, placeTok, commaTok, placeTok, cParenTok]
-- | id for the emtpy tuple
unitId :: Id
unitId       = mkId [oParenTok, cParenTok]
-- | see 'typeTok'
typeId :: Id
typeId       = mkId [placeTok, typeTok]
-- | see 'exprTok'
exprId :: Id
exprId       = mkId [exprTok]
-- | see 'varTok'
varId :: Id
varId        = mkId [varTok]
-- | see 'unknownTok'
unknownId :: Id
unknownId    = mkId [unknownTok]

listId :: (Id, Id) -> Id
listId (f,c) = Id [listTok] [f,c] nullRange

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listTok 
                        && assert (length cs == 2) True

-- | interpret placeholders as literal places
protect :: Id -> Id
protect i = Id [protectTok] [i] nullRange

unProtect :: Id -> Id
unProtect (Id _ [i] _) = i
unProtect _ = error "unProtect"

isProtected :: Id -> Bool
isProtected (Id ts cs _) = not (null ts) && head ts == protectTok
                           && isSingle cs

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
             then assert (isSingle ra) $ head ra
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
scanItem addType ks (trm, t) p =
    let ts = rest p
        as = args p
        ide = rule p
        q = p { posList = tokPos t `appRange` posList p }
    in if null ts then [] else 
          let tt = tail ts
              r = q { rest = tt }
              in
          if head ts == t then 
               if t == commaTok then
                  assert (not $ null tt) $ 
                  if head tt == termTok then
               -- tuple or list elements separator 
                  [ r, q { rest = termTok : ts } ]
                  else [r] 
              else if t == exprTok || t == varTok then 
                   [r { args = trm : args p }]
              else if t == typeTok then 
                   assert (null tt && isSingle as) $
                   [q { rest = [], args = [addType trm $ head as] }]
              else [r]
          else if Set.null ks then []
               else if isUnknownId ide
                 && not (tokStr t `Set.member` ks) then
               [r { rule = mkId [unknownTok, t]}]
               else []

scan :: (a -> a -> a) -> Knowns -> (a, Token) -> [Item a] -> [Item a] 
scan f ks term = concatMap (scanItem f ks term)

mkAmbigs :: ToExpr a -> Item a -> [a]
mkAmbigs toExpr p = 
    let l = args p in
    map ( \ aas -> fst $ 
          mkExpr toExpr 
          p { args = take (length l - length aas) l ++ aas
            } ) $ ambigArgs p

addArg :: GlobalAnnos -> ToExpr a -> Item a -> Item a -> Item a
addArg ga toExpr argItem p = 
    let (arg, ps) = mkExpr toExpr argItem 
        ams = ambigs argItem
        newAms = mkAmbigs toExpr argItem
        pArgs = args p 
        op = rule p
        num = length pArgs
        q = assert (not $ null $ rest p) $
               p { rest = tail $ rest p
                 , posList = ps `appRange` posList p
                 , args = arg : pArgs 
                 , ambigs = (if null newAms then ams else newAms : ams)
                   ++ ambigs p }
        in if isLeftArg op num then 
              q { lWeight = getNewWeight ALeft ga argItem op }
           else if isRightArg op num then
                q { rWeight = getNewWeight ARight ga argItem op }
           else q 

-- | shortcut for a function that constructs an expression
type ToExpr a = Id -> [a] -> Range -> a 

mkExpr :: ToExpr a -> Item a -> (a, Range)
mkExpr toExpr itm = 
    let orig = rule itm
        ps = posList itm
        rs = reverseRange ps
        (ide, qs) = if isListId orig then (orig, rs) else
                     if isProtected orig then 
                       setPlainIdePos (unProtect orig) rs
                    else setPlainIdePos orig rs
        as = reverse $ args itm
        in (asListAppl toExpr ide as qs, rs)

reduce :: GlobalAnnos -> Table a -> ToExpr a -> Item a -> [Item a]
reduce ga table toExpr itm = 
    map (addArg ga toExpr itm)
        $ filter ( \ oi ->  let ts = rest oi in
                   if null ts then False
                   else if head ts == termTok
                   then checkPrecs ga itm oi
                   else False )
        $ lookUp table $ index itm

-- | 'Id' starts with a 'place'
begPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)

-- | 'Id' ends with a 'place'
endPlace :: Id -> Bool
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

-- | check if a left argument will be added.
-- (The 'Int' is the number of current arguments.)
isLeftArg :: Id -> Int -> Bool
isLeftArg op num = begPlace op && num == 0
-- | check if a right argument will be added.
isRightArg :: Id -> Int -> Bool
isRightArg op num = endPlace op && num + 1 == placeCount op

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
checkArg side ga argItem opItem =
    let op = rule opItem
        opPrec = info opItem
        arg = rule argItem
        argPrec = info argItem
        precs = prec_annos ga
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
checkPrecs ga argItem opItem =
    let op = rule opItem
        num = length $ args opItem 
    in if isLeftArg op num then 
          checkArg ARight ga argItem opItem
       else if isRightArg op num then
            checkArg ALeft ga argItem opItem
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
    if any ( \ p -> let ts = rest p in
            not (null ts) && head ts == termTok) items 
    then rs ++ items
    else items

ordItem :: Item a -> Item a -> Ordering
ordItem i1 i2 = 
    compare (index i1, rest i1, rule i1)
                (index i2, rest i2, rule i2)

ambigItems :: Item a -> Item a -> Item a
ambigItems i1 i2 = let as = ambigArgs i1 ++ ambigArgs i2 in
                       i1 { ambigArgs = if null as then 
                            [args i1, args i2] else as }

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
        in if null items 
           then Result ds Nothing
           else let (finals, rest1) = partition ((startIndex==) . index) items
                    (result, rest2) = partition (null . rest) finals
                    in if null result then 
                          let expected = if null rest2 
                                         then filter (not . null . rest) rest1 
                                         else rest2 
                              withpos = filter (not . isNullRange . posList) expected
                              (q, errs) = if null withpos then (p, expected) 
                                            else (concatMapRange (reverseRange .  
                                                  posList) withpos, withpos)
                              in Result (Diag Error 
                               ("expected further mixfix token: " 
                                ++ show (take 5 $ nub 
                                        $ map (tokStr . head . rest) 
                                         errs)) q : ds) Nothing
                       else if null $ tail result then
                            let har = head result 
                                ams = ambigs har
                                ambAs = mkAmbigs toExpr har
                                res = Just $ fst $ mkExpr toExpr har
                                in 
                                if null ams then 
                                   if null ambAs then
                                      Result ds res
                                   else Result ((showAmbigs pp p $ 
                                             take 5 ambAs) : ds) res
                                else Result ((map (showAmbigs pp p) $ 
                                             take 5 ams) ++ ds) res
                       else Result ((showAmbigs pp p $
                            map (fst . mkExpr toExpr) result) : ds) Nothing 
                                   
showAmbigs :: (a -> ShowS) -> Range -> [a] -> Diagnosis
showAmbigs pp p as = 
    Diag Error ("ambiguous mixfix term\n  " ++ 
                showSepList (showString "\n  ") pp
                (take 5 as) "") p

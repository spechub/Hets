
{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable
    
   generic mixfix analysis

   - Ambiguities are not removed yet and may cause explosion

   - filtering by longest id is not symmetric

   todo: move 'getTokenList' and 'setIdePos' stuff from 'Id' into this module

-}

module Common.Earley (
                     -- * special tokens for special ids
                     varTok, exprTok, typeTok
		     , applId, parenId, typeId, exprId, varId
		     , tupleId, unitId, unknownId
		     , Knowns
		     , mkRuleId
		     , listRules
		     , getTokenPlaceList
                     -- * resolution chart
		     , Chart
		     , mixDiags
		     , ToExpr
		     , initChart
		     , nextChart
		     , getResolved)
    where

import Common.Id
import Common.Result
import Common.Precedence
import Common.GlobalAnnotations
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Data.List
-- import Control.Exception (assert)
-- import Debug.Trace(trace)

assert :: Bool -> a -> a
assert b a = if b then a else error ("assert")

-- | a special index type for more type safety
newtype Index = Index Int deriving (Eq, Ord, Show)

-- deriving Num is also possible  
-- but the following functions are sufficient
-- | the initial index
startIndex :: Index
startIndex = Index 0

incrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)

data Item a b = Item 
    { rule :: Id        -- the rule to match
    , info :: b         -- additional info for 'rule'
    , posList :: [Pos]  -- positions of Id tokens
    , args :: [a]       -- currently collected arguments 
      -- both in reverse order
    , ambigs :: [[a]]   -- currently unused fields for ambiguities
    , rest :: [Token]   -- part of the rule after the "dot"
    , index :: Index    -- index into the Table/input string
    }

instance Show (Item a b) where
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
listToken :: Token 
listToken = mkSimpleId "[]"

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

-- | construct an 'Id' from a token list
mkRuleId :: [Token] -> Id
mkRuleId toks = Id toks [] []
-- | the invisible application rule with two places
applId :: Id
applId       = mkRuleId [placeTok, placeTok]
-- | parenthesis around one place
parenId :: Id
parenId      = mkRuleId [oParenTok, placeTok, cParenTok]
-- | id for tuples with at least two arguments
tupleId :: Id
tupleId      = mkRuleId [oParenTok, placeTok, commaTok, placeTok, cParenTok]
-- | id for the emtpy tuple
unitId :: Id
unitId       = mkRuleId [oParenTok, cParenTok]
-- | see 'typeTok'
typeId :: Id
typeId       = mkRuleId [placeTok, typeTok]
-- | see 'exprTok'
exprId :: Id
exprId	     = mkRuleId [exprTok]
-- | see 'varTok'
varId :: Id
varId	     = mkRuleId [varTok]
-- | see 'unkownTok'
unknownId :: Id
unknownId    = mkRuleId [unknownTok]

listId :: (Id, Id) -> Id
-- unique id (usually "[]" yields two tokens)
listId (f,c) = Id [listToken] [f,c] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken 
			&& assert (length cs == 2) True

isUnknownId :: Id -> Bool
isUnknownId (Id ts _ _) = not (null ts) && head ts == unknownTok

mkItem :: Index -> (Id, b, [Token]) -> Item a b
mkItem ind (ide, inf, toks) = 
    Item { rule = ide
	 , info = inf
	 , posList = []
	 , args = []
	 , ambigs = []
	 , rest = toks
	 , index = ind }

-- | extract tokens with the non-terminal for places 
getTokenPlaceList :: Id -> [Token]
getTokenPlaceList = getTokenList termStr

asListAppl :: ToExpr a b -> Id -> b -> [a] -> [Pos] -> a
asListAppl toExpr i b ra br =
    if isListId i then    
           let Id _ [f, c] _ = i
	       mkList [] ps = toExpr c b [] ps
	       mkList (hd:tl) ps = toExpr f b [hd, mkList tl ps] ps
	   in mkList ra br
    else if i == typeId
	     || i == exprId 
	     || i == parenId
	     || i == varId
	     then assert (isSingle ra) $ head ra
	     else toExpr i b ra br

-- | construct the list rules
listRules :: b -> GlobalAnnos -> [(Id, b, [Token])]
listRules inf g = 
    let lists = list_lit $ literal_annos g
        listRule co toks = (listId co, inf, toks)
    in concatMap ( \ (bs, n, c) ->
       let (b1, b2, cs) = getListBrackets bs 
	   e = Id (b1 ++ b2) cs [] in
	   (if e == n then [] -- add b1 ++ b2 if its not yet included by n
	       else [listRule (c, n) $ getPlainTokenList e]) 
	   ++ [listRule (c, n) (b1 ++ [termTok] ++ b2), 
	       listRule (c, n) (b1 ++ [termTok, commaTok, termTok] ++ b2)]
		 ) $ Set.toList lists

type Table a b = Map.Map Index [Item a b]

lookUp :: Table a b -> Index -> [Item a b]
lookUp ce k = Map.findWithDefault [] k ce

-- | a set of strings that do not match a 'unknownTok'
type Knowns = Set.Set String

-- | recognize next token (possible introduce new tuple variable)
scanItem :: (a -> a -> a) -> Knowns -> (a, Token) -> Item a b
	  -> [Item a b] 
scanItem addType knowns (trm, t) p =
    let ts = rest p
	as = args p
	ide = rule p
	q = p { posList = tokPos t : posList p }
    in if null ts then [] else 
	  if head ts == t then 
	       if t == commaTok then
	       -- tuple or list (or compound) elements separator 
		  [ q { rest = termTok : ts }
		  , q { rest = tail ts }]
              else if t == exprTok || t == varTok then 
		   [q { rest = tail ts, args = trm : args p }]
              else if t == typeTok then 
		   assert (null (tail ts) && isSingle as) $
		   [q { rest = [], args = [addType trm $ head as] }]
	      else [q { rest = tail ts}]
	  else if isUnknownId ide
	         && not (tokStr t `Set.member` knowns) then
	       [q { rest = tail ts
		  , rule = mkRuleId [unknownTok, t]}]
	       else []

scan :: (a -> a -> a) -> Knowns -> (a, Token) -> [Item a b]
     -> [Item a b] 
scan f knowns term = concatMap (scanItem f knowns term)

addArg :: [[a]] -> (a, Pos) -> Item a b -> Item a b
addArg ams (arg, q) p = assert (not $ null $ rest p) $
               p { rest = tail $ rest p
		 , posList = q : posList p
		 , args = arg : args p 
		 , ambigs = ams ++ ambigs p }

-- | shortcut for a function that constructs an expression
type ToExpr a b = Id -> b -> [a] -> [Pos] -> a 

mkExpr :: ToExpr a b -> Item a b -> (a, Pos)
mkExpr toExpr item = 
    let orig = rule item
	ps = posList item
	rs = reverse ps
	(ide, qs) = if isListId orig then (orig, rs) else
		    setPlainIdePos orig rs
	inf =  info item
	as = reverse $ args item
	in (asListAppl toExpr ide inf as qs, head qs)

reduce :: GlobalAnnos -> Table a b -> (b -> b -> Maybe Bool) 
       -> ToExpr a b -> Item a b -> [Item a b]
reduce ga table filt toExpr item = 
    let ide = rule item
	inf = info item
    in map (addArg (ambigs item) $ mkExpr toExpr item)
	$ filter ( \ oi ->  let ts = rest oi in
		   if null ts then False
		   else if head ts == termTok
		   then case filt inf $ info oi of 
		   Nothing -> checkPrecs ga ide (rule oi) 
		              $ length $ args oi
		   Just b -> b 
		   else False )
	$ lookUp table $ index item

complete :: (b -> b -> Maybe Bool) -> ToExpr a b -> GlobalAnnos 
	 -> Table a b -> [Item a b] -> [Item a b]
complete filt toExpr ga table items = 
    let completedItems = filter (null . rest) items
        reducedItems = concatMap (reduce ga table filt toExpr) completedItems 
    in 	if null reducedItems 
	then items
	else complete filt toExpr ga table reducedItems ++ items

predict :: [Item a b] -> [Item a b] -> [Item a b]
predict rs items =
    if any ( \ p -> let ts = rest p in
	    not (null ts) && head ts == termTok) items 
    then rs ++ items
    else items

overlap :: Item a b -> Item a b -> Bool
overlap i1 i2 = index i1 == index i2 && rest i1 == rest i2

equivItem :: Item a b -> Item a b -> Bool
equivItem i1 i2 = overlap i1 i2 && 
		  rule i1 == rule i2

size :: Item a b -> Int
size = length . getPlainTokenList . rule 

ordItem :: Item a b -> Item a b -> Ordering
ordItem i1 i2 = 
    compare (index i1, rest i1, size i2, rule i1)
		(index i2, rest i2, size i1, rule i2)

flatItems :: ToExpr a b -> [Item a b] -> Item a b
flatItems toExpr (i:is) = 
    if null is 
    then i
    else i { ambigs = map (fst . mkExpr toExpr) (i:is) : concatMap ambigs is }
flatItems _ [] = error "flatItems: empty list"

packAmbigs :: ToExpr a b -> [Item a b] -> [Item a b]
packAmbigs toExpr = map (flatItems toExpr) . groupBy equivItem

longest :: [Item a b] -> [Item a b]
longest (i:is) =
    if null is 
    then [i]
    else if size i > size (head is) 
	 then [i]
	 else i : longest is
longest [] = error "longest: empty list"

filterLongest :: [Item a b] -> [Item a b]
filterLongest = 
    concatMap longest . groupBy overlap

-- | the whole state for mixfix resolution 
data Chart a b = Chart { prevTable :: Table a b
		       , currIndex :: Index
		       , currItems :: [Item a b]
		       , rules :: [(Id, b, [Token])]
		       , solveDiags :: [Diagnosis] }
	       deriving Show

-- | make one scan, complete, and predict step.
-- The first function adds a type to the result.
-- The second function filters based on argument and operator info.
-- If filtering yields 'Nothing' further filtering by precedence is applied. 
nextChart :: (a -> a -> a) -> (b -> b -> Maybe Bool) -> ToExpr a b 
	  -> Knowns -> GlobalAnnos -> Chart a b -> (a, Token) -> Chart a b
nextChart addType filt toExpr knowns ga st term@(_, tok) = 
    let table = prevTable st
	idx = currIndex st
	items = currItems st
	scannedItems = scan addType knowns term items
        nextTable = Map.insert idx items table
	nextIdx = incrIndex idx
    in	if null items then st else
	st { prevTable = nextTable
	   , currIndex = nextIdx
	   , currItems =  predict (map (mkItem nextIdx) $ rules st)
--	   $ packAmbigs toExpr
--	   $ filterLongest
--	   $ sortBy ordItem
	   $ complete filt toExpr ga nextTable scannedItems
	   , solveDiags = (if null scannedItems then 
		      [Diag Error ("unexpected mixfix token: " ++ tokStr tok)
		      $ tokPos tok]
		      else []) ++ solveDiags st }

-- | add intermediate diagnostic messages
mixDiags :: [Diagnosis] -> Chart a b -> Chart a b
mixDiags ds st = st { solveDiags = ds ++ solveDiags st }

-- | create the initial chart
initChart :: [(Id, b, [Token])] -> Chart a b
initChart ruleS = Chart { prevTable = Map.empty
			, currIndex = startIndex
			, currItems = map (mkItem startIndex) ruleS
			, rules = ruleS
			, solveDiags = [] }

-- | extract resolved result
getResolved :: (a -> ShowS) -> Pos -> ToExpr a b -> Chart a b 
	    -> Result a
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
			      in Result (Diag Error 
			       ("expected further mixfix token: " 
				++ show (take 5 $ nub 
					$ map (tokStr . head . rest) 
					 expected)) p : ds) Nothing
		       else if null $ tail result then
			    let har = head result 
				ams = ambigs har
				res = Just $ fst $ mkExpr toExpr har
				in 
				if null ams then 
				   Result ds res
				else Result ((map (showAmbigs pp p) $ 
					     take 5 ams) ++ ds) res
		       else Result ((showAmbigs pp p $
			    map (fst . mkExpr toExpr) result) : ds) Nothing 
				   
showAmbigs :: (a -> ShowS) -> Pos -> [a] -> Diagnosis
showAmbigs pp p as = 
    Diag Error ("ambiguous mixfix term\n\t" ++ 
		showSepList (showString "\n\t") pp
		(take 5 as) "") p


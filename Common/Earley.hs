module Common.Earley where

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

-- | test if initial (although hiding (==) seems not to be possible) 
isStartIndex :: Index -> Bool
isStartIndex = (== startIndex)

incrIndex, decrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)
decrIndex (Index i) = Index (i - 1)

data Item a b = Item 
    { rule :: Id        -- the rule to match
    , info :: b       -- additional info for 'rule'
    , posList :: [Pos]    -- positions of Id tokens
    , args :: [a]     -- currently collected arguments 
      -- both in reverse order
    , rest :: [Token] -- part of the rule after the "dot"
    , index :: Index -- index into the Table/input string
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

termStr :: String
termStr = "_"
commaTok, termTok, oParenTok, cParenTok, placeTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId termStr
placeTok = mkSimpleId place
oParenTok = mkSimpleId "(" 
cParenTok = mkSimpleId ")" 

exprTok, varTok, typeTok, unknownTok :: Token
typeTok = mkSimpleId ":"
listToken :: Token 
listToken = mkSimpleId "[]"
exprTok = mkSimpleId "(_)"
varTok = mkSimpleId "(v)"
unknownTok = mkSimpleId "(?)"

mkRuleId :: [Token] -> Id
mkRuleId toks = Id toks [] []
applId, parenId, typeId, exprId, varId, tupleId, unitId, unknownId :: Id
applId       = mkRuleId [placeTok, placeTok]
parenId      = mkRuleId [oParenTok, placeTok, cParenTok]
tupleId      = mkRuleId [oParenTok, placeTok, commaTok, placeTok, cParenTok]
unitId       = mkRuleId [oParenTok, cParenTok]
typeId       = mkRuleId [placeTok, typeTok]
exprId	     = mkRuleId [exprTok]
varId	     = mkRuleId [varTok]
unknownId    = mkRuleId [unknownTok]

listId :: Id -> Id
-- unique id (usually "[]" yields two tokens)
listId i = Id [listToken] [i] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken && isSingle cs

isUnknownId :: Id -> Bool
isUnknownId (Id ts _ _) = not (null ts) && head ts == unknownTok

mkItem :: Index -> Id -> b -> [Token] -> Item a b
mkItem ind ide inf toks = 
    Item { rule = ide
	 , info = inf
	 , posList = []
	 , args = []
	 , rest = toks
	 , index = ind }

getTokenPlaceList :: Id -> [Token]
getTokenPlaceList = getTokenList termStr

mkMixfixItem :: Index -> (Id, b) -> Item a b
mkMixfixItem i (ide, inf) = 
    mkItem i ide inf $ getTokenPlaceList ide

listStates :: b -> GlobalAnnos -> Index -> [Item a b]
listStates inf g i = 
    let lists = list_lit $ literal_annos g
        listState co toks = mkItem i (listId co) inf toks
    in concatMap ( \ (bs, n, c) ->
       let (b1, b2, cs) = getListBrackets bs 
	   e = Id (b1 ++ b2) cs [] in
	   (if e == n then [] -- add b1 ++ b2 if its not yet included by n
	       else [listState c $ getPlainTokenList e]) ++
                   [listState c (b1 ++ [termTok] ++ b2) 
		   , listState c (b1 ++ [termTok, commaTok, termTok] ++ b2)]
		   ) $ Set.toList lists


type Table a b = Map.Map Index [Item a b]

lookUp :: Table a b -> Index -> [Item a b]
lookUp ce k = Map.findWithDefault [] k ce


type Knowns = Set.Set String

-- recognize next token (possible introduce new tuple variable)
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
		   assert (null as) $
		   [p { rest = tail ts, args = [trm] }]
              else if t == typeTok then 
		   assert (null (tail ts) && isSingle as) $
		   [p { rest = [], args = [addType trm $ head as] }]
	      else [q { rest = tail ts}]
	  else if ide == unknownId 
	         && not (tokStr t `Set.member` knowns) then
	       [q { rest = tail ts
		  , rule = mkRuleId [unknownTok, t]}]
	       else []

scan :: (a -> a -> a) -> Knowns -> (a, Token) -> [Item a b]
     -> [Item a b] 
scan f knowns term = concatMap (scanItem f knowns term)

addArg :: a -> Item a b -> Item a b
addArg arg p = assert (not $ null $ rest p) $
               p { rest = tail $ rest p
		 , args = arg : args p }

checkArg :: GlobalAnnos -> Id -> Item a b -> Bool
checkArg ga arg p = 
    let ts = rest p in
	if null ts then False
	   else if head ts == termTok
		then checkPrecs ga arg (rule p) $ length $ args p
		else False

reduce :: GlobalAnnos -> Table a b -> (Item a b -> a) 
       -> Item a b -> [Item a b]
reduce ga table toExpr item = 
    map (addArg $ toExpr item)
	$ filter (checkArg ga $ rule item)
	$ lookUp table $ index item

complete :: (Item a b -> a) -> GlobalAnnos -> Table a b
	 -> [Item a b] -> [Item a b]
complete toExpr ga table items = 
    let completedItems = filter (null . rest) items
        reducedItems = concatMap (reduce ga table toExpr) completedItems 
    in 	if null reducedItems 
	then items
	else complete toExpr ga table reducedItems ++ items

predict :: [Item a b] -> [Item a b] -> [Item a b]
predict rules items =
    if any ( \ p -> let ts = rest p in
	    not (null ts) && head ts == termTok) items 
    then rules ++ items
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

flatItems :: ([a] -> a) -> [Item a b] -> Item a b
flatItems f (i:is) = 
    if null is 
    then i
    else i { args = map f (transpose (map args (i:is))) }
flatItems _ [] = error "flatItems: empty list"

packAmbigs :: ([a] -> a) -> [Item a b] -> [Item a b]
packAmbigs f = map (flatItems f) . groupBy equivItem . sortBy ordItem

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

data State a b = State { prevTable :: Table a b
		       , currIndex :: Index
		       , currItems :: [Item a b]
		       , solveDiags :: [Diagnosis] }
	       deriving Show

nextState :: (Index -> [Item a b]) -> 
	     (a -> a -> a) -> Knowns -> 
	     (Item a b -> a) -> GlobalAnnos -> 
	     State a b -> (a, Token) -> State a b
nextState fromRules addType knowns toExpr ga st term@(_, tok) = 
    let table = prevTable st
	idx = currIndex st
	items = currItems st
	scannedItems = scan addType knowns term items
        nextTable = Map.insert idx items table
	nextIdx = incrIndex idx
    in	if null items then st else
	st { prevTable = nextTable
	   , currIndex = nextIdx
	   , currItems =  predict (fromRules nextIdx)
	   $ filterLongest
	   $ sortBy ordItem
	   $ complete toExpr ga nextTable scannedItems
	   , solveDiags = (if null scannedItems then 
		      [Diag Error ("unexpected mixfix token: " ++ tokStr tok)
		      $ tokPos tok]
		      else []) ++ solveDiags st }

initState :: (Index -> [Item a b]) -> State a b
initState fromRules = State { prevTable = Map.empty
			    , currIndex = startIndex
			    , currItems = fromRules startIndex
			    , solveDiags = [] }

getResolved :: (a -> ShowS) -> Pos -> (Item a b -> a) -> State a b -> Result a
getResolved pp p toExpr st = 
    let items = filter ((currIndex st/=) . index) $ currItems st 
	ds = solveDiags st
	in if null items 
	   then Result ds Nothing
	   else let (completed, uncompleted) = partition (null . rest) items
		    finals = filter  ((startIndex==) . index) completed
		    in if null finals then 
		       Result (Diag Error 
			       ("expecting further mixfix token: " 
				++ show (nub $ map (tokStr . head . rest) 
					 uncompleted)) p : ds) Nothing
		       else if null $ tail finals then
			    Result ds $ Just $ toExpr $ head finals
		       else Result (Diag Error 
				    ("ambiguous mixfix \n\t" ++ 
				     showSepList (showString "\n\t") pp
				     (map toExpr $ take 5 finals) "") p : ds)
		            Nothing   

				   




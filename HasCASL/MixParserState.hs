
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

special parsing states for the mixfix analysis of terms

-}

module HasCASL.MixParserState where

import HasCASL.As
import HasCASL.Le
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Data.Maybe
import HasCASL.Unify

-- avoid confusion with the variable counter Int
newtype Index = Index Int deriving (Eq, Ord, Show)

-- deriving Num is also possible  
-- but the following functions are sufficient
startIndex :: Index
startIndex = Index 0

-- (also hiding (==) seems not possible) 
isStartIndex :: Index -> Bool
isStartIndex = (== startIndex)

incrIndex, decrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)
decrIndex (Index i) = Index (i - 1)

data PState a = PState { ruleId :: Id        -- the rule to match
		     , ruleScheme :: TypeScheme -- to make id unique
                     , ruleType :: Type    -- type of Id
                     , posList :: [Pos]    -- positions of Id tokens
		     , ruleArgs :: [a]  -- currently collected arguments 
		                           -- both in reverse order
		     , restRule :: [Token] -- part of the rule after the "dot"
		     , stateNo :: Index -- index into the ParseMap/input string
		     }

instance Eq (PState a) where
    PState r1 s1 _ _ _ t1 p1 == PState r2 s2 _ _ _ t2 p2 =
	(r1, s1, t1, p1) == (r2, s2, t2, p2)

instance Show (PState a) where
    showsPrec _ p = 
	let d = restRule p
	    v = getPlainTokenList (ruleId p)
	    first = take (length v - length d) v
	    Index i = stateNo p 
	    in showChar '{' 
			  . showSepList (showString "") showTok first
			  . showChar '.' 
			  . showSepList (showString "") showTok d
			  . shows i . showChar '}'
                          . showChar ':' 
	                  . showPretty (ruleType p)  



termStr :: String
termStr = "_"
commaTok, termTok, oParenTok, cParenTok, placeTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId termStr
placeTok = mkSimpleId place
oParenTok = mkSimpleId "(" 
cParenTok = mkSimpleId ")" 

opTok, inTok, caseTok, unknownTok :: Token
inTok = mkSimpleId "in"
caseTok = mkSimpleId "case"
opTok = mkSimpleId "(o)"
unknownTok = mkSimpleId "(?)"

mkRuleId :: [Token] -> Id
mkRuleId toks = Id toks [] []
applId, parenId, inId, opId, tupleId, unitId, unknownId :: Id
applId       = mkRuleId [placeTok, placeTok]
parenId      = mkRuleId [oParenTok, placeTok, cParenTok]
tupleId      = mkRuleId [oParenTok, placeTok, commaTok, cParenTok]
unitId       = mkRuleId [oParenTok, cParenTok]
inId  	     = mkRuleId [inTok]
opId	     = mkRuleId [opTok]
unknownId    = mkRuleId [unknownTok]

mkPState :: Index -> Id -> TypeScheme -> Type -> [Token] -> PState a
mkPState ind ide sc ty toks = 
    PState { ruleId = ide
	   , ruleScheme = sc
	   , ruleType = ty
	   , posList = []
	   , ruleArgs = []
	   , restRule = toks
	   , stateNo = ind }

mkMixfixState :: Index -> (Id, OpInfo) -> State Int (PState a)
mkMixfixState i (ide, info) = 
    do let sc = opType info
       t <- freshInst sc
       let stripped = case t of 
			     FunType t1 _ _ _ -> 
				 case t1 of 
					 ProductType _ _ -> ide
					 _ -> stripFinalPlaces ide
			     _ -> stripFinalPlaces ide
       return $ mkPState i stripped sc t $ getTokenList termStr stripped

mkPlainApplState :: Index -> (Id, OpInfo) -> State Int (PState a) 
mkPlainApplState i (ide, info) =     
    do let sc = opType info
       t <- freshInst sc
       return $ mkPState i ide sc t $ getPlainTokenList ide

listToken :: Token 
listToken = mkSimpleId "[]"
listId :: Id -> Id
-- unique id (usually "[]" yields two tokens)
listId i = Id [listToken] [i] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken && isSingle cs

isUnknownId :: Id -> Bool
isUnknownId (Id ts _ _) = not (null ts) && head ts == unknownTok

listStates :: GlobalAnnos -> Index -> State Int [PState a]
-- no empty list (can be written down directly)
listStates g i = 
    do tvar <- freshVar
       let ty = TypeName tvar star 1
	   lists = list_lit $ literal_annos g
	   listState co toks = mkPState i (listId co) (simpleTypeScheme $ 
					   BracketType Squares [] []) 
			       ty toks
	   in return $ concatMap ( \ (bs, n, c) ->
	     let (b1, b2, cs) = getListBrackets bs 
		 e = Id (b1 ++ b2) cs [] in
	     (if e == n then [] -- add b1 ++ b2 if its not yet included by n
	      else [listState c $ getPlainTokenList e]) ++
                   [listState c (b1 ++ [termTok] ++ b2) 
		   , listState c (b1 ++ [termTok, commaTok] ++ b2)]
		   ) $ Set.toList lists

-- these are the possible matches for the nonterminal (T)
-- the same states are used for the predictions  


mkTokState :: Index -> Id -> State Int (PState a) 
mkTokState i r = 
    do tvar <- freshVar
       let ty = TypeName tvar star 1
           sc = simpleTypeScheme ty
       return $ mkPState i r sc ty $ getTokenList termStr r

mkApplTokState :: Index -> Id -> State Int (PState a) 
mkApplTokState i r = 
    do tv1 <- freshVar
       tv2 <- freshVar
       let ty1 = TypeName tv1 star 1
	   ty2 = TypeName tv2 star 1
	   tappl = FunType ty1 PFunArr ty2 []
	   t2appl = FunType tappl PFunArr tappl []
           sc = simpleTypeScheme t2appl
       return $ mkPState i r sc t2appl $ getTokenList termStr r

mkTupleTokState :: Index -> Id -> State Int (PState a) 
mkTupleTokState i r = 
    do tv1 <- freshVar
       tv2 <- freshVar
       let ty1 = TypeName tv1 star 1
	   ty2 = TypeName tv2 star 1
	   tuple = ProductType [ty1, ty2] []
	   tappl = FunType ty1 PFunArr (FunType ty2 PFunArr tuple []) []
           sc = simpleTypeScheme tappl
       return $ mkPState i r sc tappl $ getTokenList termStr r


mkParenTokState :: Index -> Id -> State Int (PState a) 
mkParenTokState i r = 
    do tv1 <- freshVar
       let ty1 = TypeName tv1 star 1
	   tappl = FunType ty1 PFunArr ty1 []
           sc = simpleTypeScheme tappl
       return $ mkPState i r sc tappl $ getTokenList termStr r

initialState :: GlobalAnnos -> Assumps -> Index -> State Int [PState a]
initialState g as i = 
    do let ids = concatMap (\ (ide, l) -> map ( \ e -> (ide, e)) $ opInfos l) 
		 $ Map.toList as
       ls <- listStates g i
       l1 <- mapM (mkMixfixState i) ids
       l2 <- mapM (mkPlainApplState i) $ filter (isMixfix . fst) ids
       a  <- mkApplTokState i applId
       p  <- mkParenTokState i parenId
       t  <- mkTupleTokState i tupleId
       l3 <- mapM (mkTokState i)
              [unitId,
	       inId,
	       opId]
       return (a:p:t:ls ++ l1 ++ l2 ++ l3)

type Knowns = Set.Set String -- cannot be unknown variables

-- recognize next token (possible introduce new tuple variable)
scanState :: TypeMap -> Knowns -> (Maybe Type, a) -> Token -> PState a
	  -> State Int [PState a]
scanState tm knowns (mty, trm) t p =
    do let ts = restRule p
       if null ts then return [] else 
	  if head ts == t then 
	       if t == commaTok then -- tuple elements separator 
	       do tvar <- freshVar
		  let nextTy = TypeName tvar star 1
                      newTy = case ruleType p of 
	                  FunType lastTy PFunArr (ProductType tys ps) _ -> 
	                      FunType lastTy PFunArr 
					  (FunType nextTy PFunArr
		                           (ProductType (tys++[nextTy]) ps)
					   []) []
	                  _ -> error "scanState"
		  return [ p { restRule = termTok : commaTok : tail ts
			     , ruleType = newTy }
			 , p { restRule = termTok : tail ts }]
              else return $
		   if t == opTok || t == inTok then
	             let Just ty = mty 
                         mp = do q <- filterByType tm (ty,trm) p
	                         return q { ruleType = ty, restRule = tail ts }
	             in maybeToList mp
 	      else case mty of
	           Nothing -> [p { restRule = tail ts
			         , posList = tokPos t : posList p }]
		   Just ty -> maybeToList 
		       (do q <- filterByType tm (ty,trm) p
			   return q { ruleType = ty, restRule = tail ts
                                    , posList = tokPos t : posList q })
	  else return $ if ruleId p == unknownId 
	         && not (tokStr t `Set.member` knowns) then
	       [p { restRule = tail ts, posList = tokPos t : posList p
		  , ruleId = mkRuleId [unknownTok, t]
		  , ruleType = case mty of 
		               Nothing -> ruleType p
		               Just ty -> ty }]
	       else []

-- construct resulting term from PState 

stateToAppl :: PState Term -> Term
stateToAppl p = 
    let r = ruleId p
        sc@(TypeScheme _ (_ :=> ty) _) = ruleScheme p
        ar = reverse $ ruleArgs p
	qs = reverse $ posList p
    in if  r == inId 
	   || r == parenId 
	   || r == opId 
       then head ar
       else if r == applId then
	    ApplTerm (head ar) (head (tail ar)) qs 
       else if r == tupleId || r == unitId then TupleTerm ar qs
       else addFunArguments (ty, QualOp (InstOpId (setIdePos r ar qs) [] []) 
			     sc qs) 
		$ concatMap expandArgument ar

expandArgument :: Term -> [Term]
expandArgument arg =
    case arg of 
             TupleTerm ts _ -> concatMap expandArgument ts
	     _ -> [arg]

addFunArguments :: (Type, Term) -> [Term] -> Term
addFunArguments (ty, trm) args =
    if null args then trm else
    case ty of 
	    FunType t1 _ t2 _ -> 
		let arg: rest = getArgument t1 args in
		    addFunArguments (t2, ApplTerm trm arg []) rest
	    _ -> error "addFunArguments"

getArgument :: Type -> [Term] -> [Term]
getArgument ty args =
    case ty of
	     ProductType ts _ -> 
		 let (trms, rest) = getArguments ts args in 
		     TupleTerm trms [] : rest
	     _ -> if null args then error "getArgument" 
		  else args

getArguments :: [Type] -> [Term] -> ([Term], [Term])
getArguments [] args = ([], args)
getArguments (t:rt) args = 
    let trm : restArgs = getArgument t args
	(nextTrms, finalArgs) = getArguments rt restArgs
    in (trm:nextTrms, finalArgs)
 
toAppl :: GlobalAnnos -> PState Term -> Term
toAppl g s = let i = ruleId s in
    if isListId i then    
           let Id _ [f] _ = i
	       ListCons b c = getLiteralType g f
	       (b1, _, _) = getListBrackets b
	       cl = length $ getPlainTokenList b
               nb1 = length b1
               ra = reverse $ ruleArgs s
               na = length ra
	       br = reverse $ posList s
               nb = length br
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null ra then asAppl c [] 
		  (if null br then nullPos else head br)
	      else if nb + 2 == cl + na then
		   let br1 = drop (nb1 - 1) br 
	           in  mkList ra br1  
		   else error "toAppl"
    else stateToAppl s

asAppl :: Id -> [Term] -> Pos -> Term
asAppl f args p = let pos = if null args then [] else [p]
		  in ApplTerm (QualOp (InstOpId f [] [])
			       (simpleTypeScheme $ MixfixType []) 
			       []) (TupleTerm args []) pos

-- precedence graph stuff

checkArg :: GlobalAnnos -> AssocEither -> Id -> Id -> Bool
checkArg g dir op arg = 
    if arg == op 
       then isAssoc dir (assoc_annos g) op || not (isInfix op)
       else 
       case precRel (prec_annos g) op arg of
       Lower -> True
       Higher -> False
       BothDirections -> False
       NoDirection -> not $ isInfix arg

checkAnyArg :: GlobalAnnos -> Id -> Id -> Bool
checkAnyArg g op arg = 
    case precRel (prec_annos g) op arg of
    BothDirections -> isInfix op && op == arg
    _ -> True				       

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
filterByPrec :: GlobalAnnos -> Id -> PState a -> Bool
filterByPrec g argIde  
		 PState { ruleId = opIde, ruleArgs = args, restRule = ts } =
    if null ts then False else
       if head ts == termTok then 
	  if isUnknownId opIde then False else
	  if opIde == applId then not (null args && isUnknownId argIde) else
	  if isListId opIde || isListId argIde then True
	  else let n = length args in
		    if isLeftArg opIde n then 
		       if isPostfix opIde && (isPrefix argIde
					      || isInfix argIde) then False
		       else checkArg g ALeft opIde argIde 
		    else if isRightArg opIde n then 
                            if isPrefix opIde && isInfix argIde then False
	                    else checkArg g ARight opIde argIde
                         else checkAnyArg g opIde argIde
       else False

expandType :: TypeMap -> Type -> Type
expandType tm oldT = 
    case oldT of 
	   TypeName _ _ _ -> fst $ expandAlias tm oldT
	   KindedType t _ _ -> t
	   LazyType t _ -> t
	   _ -> oldT

addArgState :: a -> PState a -> PState a
addArgState arg op = op { ruleArgs = arg : ruleArgs op }

filterByType :: TypeMap -> (Type, a) -> PState a -> Maybe (PState a)
filterByType tm argState@(_, argTerm) opState =
	case expandType tm $ ruleType opState of
		FunType t1 _ t2 _ -> 
		    filterByArgument tm t1 [] t2 argState opState
		TypeName _ _ v -> if v == 0 then Nothing
				  else Just $ addArgState argTerm opState
		_ -> Nothing

filterByArgument :: TypeMap -> Type -> [Type] -> Type -> (Type, a) 
		 -> PState a -> Maybe (PState a)
filterByArgument tm t1 tl t2 argState@(argType, argTerm) opState =
    let ms = maybeResult $ unify tm t1 argType in 
	case ms of 
	Nothing -> 
	           case expandType tm t1 of 
		   ProductType (t:ts) _ -> filterByArgument tm t 
					   (ts++tl) t2 argState opState
		   _ -> Nothing
	Just s -> let newType = subst s $ foldr 
			      ( \ t ty -> FunType t PFunArr ty []) t2 tl
			  in return $ addArgState argTerm opState 
				 {ruleType = newType}

filterByResultType :: TypeMap -> Type -> PState a -> Maybe (PState a)
filterByResultType tm ty p = 
    do let rt = ruleType p 
       s <- maybeResult $ unify tm ty rt
       return p { ruleType = subst s rt } 

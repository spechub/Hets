
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

incrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)

data PState = PState { ruleId :: Id        -- the rule to match
		     , ruleScheme :: TypeScheme -- to make id unique
                     , ruleType :: Type    -- type of Id
                     , posList :: [Pos]    -- positions of Id tokens
		     , ruleArgs :: [Term]  -- currently collected arguments 
		                           -- both in reverse order
		     , restRule :: [Token] -- part of the rule after the "dot"
		     , stateNo :: Index -- index into the ParseMap/input string
		     }

instance Eq PState where
    PState r1 s1 _ _ _ t1 p1 == PState r2 s2 _ _ _ t2 p2 =
	(r1, s1, t1, p1) == (r2, s2, t2, p2)

instance Show PState where
    showsPrec _ p = 
	let d = restRule p
	    v = getTokenList place (ruleId p)
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

colonTok, asTok, varTok, opTok, predTok, inTok, caseTok :: Token
colonTok = mkSimpleId ":"
asTok = mkSimpleId "as"
inTok = mkSimpleId "in"
caseTok = mkSimpleId "case"
varTok = mkSimpleId "(v)"
opTok = mkSimpleId "(o)"
predTok = mkSimpleId "(p)"

mkRuleId :: [Token] -> Id
mkRuleId toks = Id toks [] []
applId, parenId, colonId, asId, inId, varId, opId, tupleId, unitId :: Id
applId       = mkRuleId [placeTok, placeTok]
parenId      = mkRuleId [oParenTok, placeTok, cParenTok]
tupleId      = mkRuleId [oParenTok, placeTok, commaTok, cParenTok]
unitId       = mkRuleId [oParenTok, cParenTok]
colonId      = mkRuleId [placeTok, colonTok]
asId         = mkRuleId [placeTok, asTok]
inId  	     = mkRuleId [placeTok, inTok]
varId	     = mkRuleId [varTok]
opId	     = mkRuleId [opTok]

mkPState :: Index -> Id -> TypeScheme -> Type -> [Token] -> PState
mkPState ind ide sc ty toks = 
    PState { ruleId = ide
	   , ruleScheme = sc
	   , ruleType = ty
	   , posList = []
	   , ruleArgs = []
	   , restRule = toks
	   , stateNo = ind }

mkMixfixState :: Index -> (Id, OpInfo) -> State Int PState 
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

mkPlainApplState :: Index -> (Id, OpInfo) -> State Int PState 
mkPlainApplState i (ide, info) =     
    do let sc = opType info
       t <- freshInst sc
       return $ mkPState i ide sc t $ getTokenList place ide

listToken :: Token 
listToken = mkSimpleId "[]"
listId :: Id -> Id
-- unique id (usually "[]" yields two tokens)
listId i = Id [listToken] [i] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken && length cs == 1

listStates :: GlobalAnnos -> Index -> State Int [PState]
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
	      else [listState c $ getTokenList place e]) ++
                   [listState c (b1 ++ [termTok] ++ b2) 
		   , listState c (b1 ++ [termTok, commaTok] ++ b2)]
		   ) $ Set.toList lists

-- these are the possible matches for the nonterminal (T)
-- the same states are used for the predictions  


mkTokState :: Index -> Id -> State Int PState 
mkTokState i r = 
    do tvar <- freshVar
       let ty = TypeName tvar star 1
           sc = simpleTypeScheme ty
       return $ mkPState i r sc ty $ getTokenList termStr r

mkApplTokState :: Index -> Id -> State Int PState 
mkApplTokState i r = 
    do tv1 <- freshVar
       tv2 <- freshVar
       let ty1 = TypeName tv1 star 1
	   ty2 = TypeName tv2 star 1
	   tappl = FunType ty1 PFunArr ty2 []
	   t2appl = FunType tappl PFunArr tappl []
           sc = simpleTypeScheme t2appl
       return $ mkPState i r sc t2appl $ getTokenList termStr r

mkTupleTokState :: Index -> Id -> State Int PState 
mkTupleTokState i r = 
    do tv1 <- freshVar
       tv2 <- freshVar
       let ty1 = TypeName tv1 star 1
	   ty2 = TypeName tv2 star 1
	   tuple = ProductType [ty1, ty2] []
	   tappl = FunType tuple PFunArr tuple []
           sc = simpleTypeScheme tappl
       return $ mkPState i r sc tappl $ getTokenList termStr r


mkParenTokState :: Index -> Id -> State Int PState 
mkParenTokState i r = 
    do tv1 <- freshVar
       let ty1 = TypeName tv1 star 1
	   tappl = FunType ty1 PFunArr ty1 []
           sc = simpleTypeScheme tappl
       return $ mkPState i r sc tappl $ getTokenList termStr r

initialState :: GlobalAnnos -> Assumps -> Index -> State Int [PState]
initialState g as i = 
    do let ids = concatMap (\ (ide, l) -> map ( \ e -> (ide, e)) l) 
		 $ Map.toList as
       ls <- listStates g i
       l1 <- mapM (mkMixfixState i) ids
       l2 <- mapM (mkPlainApplState i) $ filter (isMixfix . fst) ids
       a  <- mkApplTokState i applId
       p  <- mkParenTokState i parenId
       t  <- mkTupleTokState i tupleId
       l3 <- mapM (mkTokState i)
              [unitId,
	       colonId,
	       asId,
	       inId,
	       varId,
	       opId]
       return (a:p:t:ls ++ l1 ++ l2 ++ l3)

-- construct resulting term from PState 

stateToAppl :: PState -> Term
stateToAppl p = 
    let r = ruleId p
        ar = reverse $ ruleArgs p
	qs = reverse $ posList p
    in if r == colonId 
	   || r == asId 
	   || r == inId 
	   || r == parenId 
	   || r == varId 
	   || r == opId 
       then head ar
       else if r == applId then
	    ApplTerm (head ar) (head (tail ar)) qs 
       else if r == tupleId || r == unitId then TupleTerm ar qs
       else foldr (\ (a, q) t -> ApplTerm t a [q]) 
		(QualOp (InstOpId (ruleId p) [] []) (ruleScheme p) qs) 
		$ zip ar (posList p ++ repeat (if null qs then nullPos
					       else last qs))
	       
toAppl :: GlobalAnnos -> PState -> Term
toAppl g s = let i = ruleId s in
    if isListId i then    
           let Id _ [f] _ = i
	       ListCons b c = getLiteralType g f
	       (b1, _, _) = getListBrackets b
	       cl = length $ getTokenList place b
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
	  
filterByPrec :: GlobalAnnos -> Id -> PState -> Bool
filterByPrec g argIde  
		 PState { ruleId = opIde, ruleArgs = args, restRule = ts } =
    if null ts then False else
       if head ts == termTok then 
	  if isListId opIde || isListId argIde || opIde == applId then True
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

addArgState :: Term -> PState -> PState
addArgState arg op = op { ruleArgs = arg : ruleArgs op }

mkTupleTerm :: TypeMap -> [Type] -> (Type, Term) -> PState 
	    -> [Term] -> [Term] -> Type -> Maybe PState
mkTupleTerm tm types (ty, singleArg) op prevTerms prevArgs argType =
    let n = length prevTerms 
	fini = n + 1 == length types in
    if n >= length types then Nothing 
    else do s <- maybeResult $ unify tm (types !! n) ty
	    let argTerms = (if fini then reverse else id)
			   (singleArg : prevTerms)
		argTerm = if fini then if n == 0 then singleArg 
			               else TupleTerm argTerms []
			  else MixfixTerm argTerms
                newType = subst s (if fini then argType else
				  FunType (ProductType types []) 
				  PFunArr argType [])
	    return op { ruleArgs = argTerm : prevArgs
		      , ruleType = newType }

filterByType :: TypeMap -> (Type, Term) -> PState -> Maybe PState
filterByType tm argState@(argType, argTerm) opState =
    let prevArgs = ruleArgs opState in
	case expandType tm $ ruleType opState of
		(FunType t1 _ t2 _) -> 
		    case expandType tm t1 of 
		    ProductType ts _ -> 
			case expandType tm argType of
			ProductType _ _ -> mkTupleTerm tm [t1] argState 
					   opState [] prevArgs t2
			_ -> let (prevTerms, restArgs) = 
				     if null prevArgs then ([], []) 
					else case head prevArgs of
				     MixfixTerm trms -> (trms, tail prevArgs)
				     _ -> ([], prevArgs) in
				 mkTupleTerm tm ts argState opState 
				    prevTerms restArgs t2
		    _ -> mkTupleTerm tm [t1] argState opState [] prevArgs t2
		TypeName _ _ v -> if v == 0 then Nothing
				  else Just $ addArgState argTerm opState
		_ -> Nothing

filterByResultType :: TypeMap -> Type -> PState -> Maybe PState
filterByResultType tm ty p = 
    do let rt = ruleType p 
       s <- maybeResult $ unify tm ty rt
       return p { ruleType = subst s rt } 

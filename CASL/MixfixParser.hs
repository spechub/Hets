
{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2002-2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable
    
   Mixfix analysis of terms

   Missing features:
   - the positions of ids from string, list, number and floating annotations
     is not changed within applications (and might be misleading)
   - using (Set State) instead of [State] avoids explosion
     but detection of local ambiguities (that of subterms) is more difficult,
     solution: equal list states should be merged into a single state
               that stores the local ambiguity
-}

module CASL.MixfixParser ( resolveFormula, resolveMixfix)
    where 
import CASL.AS_Basic_CASL 
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.Id
import Common.Lib.Map as Map hiding (filter, split, map)
import Common.Lib.Set as Set hiding (filter, split, single, insert)
import Common.Lexer
import Control.Monad
import Common.Lib.Parsec
import qualified Data.Char as C
import Data.List(intersperse)
import CASL.Formula(updFormulaPos)
import qualified CASL.ShowMixfix as ShowMixfix (showTerm)

showTerm :: GlobalAnnos -> TERM -> String
showTerm _ t = ShowMixfix.showTerm t ""

-- Earley Algorithm

data State = State (Id, Bool)  -- True means predicate
                   [Pos]    -- positions of Id tokens
                   [TERM]   -- currently collected arguments 
		                               -- both in reverse order
		   [Token]  -- only tokens after the "dot" are given 
		   Int      -- index into the ParseMap/input string

instance Eq State where
    State r1 _ _ t1 p1 == State r2 _ _ t2 p2 = (r1, t1, p1) == (r2, t2, p2)

instance Ord State where
    State r1 _ _ t1 p1 <= State r2 _ _ t2 p2 = (r1, t1, p1) <= (r2, t2, p2)

termStr :: String
termStr = "(T)"
commaTok, parenTok, termTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId termStr
parenTok = mkSimpleId "(..)" 

colonTok, asTok, varTok, opTok, predTok :: Token
colonTok = mkSimpleId ":"
asTok = mkSimpleId "as"
varTok = mkSimpleId "(v)"
opTok = mkSimpleId "(o)"
predTok = mkSimpleId "(p)"

mkState :: Int -> Bool -> Id -> State 
mkState i b ide = State (ide, b) [] [] (getTokenList termStr ide) i

mkApplState :: Int -> Bool -> Id -> State
mkApplState i b ide = State (ide, b) [] [] 
		    (getPlainTokenList ide ++ [parenTok]) i


listToken :: Token 
listToken = mkSimpleId "[]"
listId :: Id -> Id
-- unique id (usually "[]" yields two tokens)
listId i = Id [listToken] [i] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken && isSingle cs

listStates :: GlobalAnnos -> Int -> [State]
listStates g i = 
    let lists = list_lit $ literal_annos g
        listState co toks = State (listId co, False) [] [] toks i
    in concatMap ( \ (bs, n, c) ->
       let (b1, b2, cs) = getListBrackets bs 
	   e = Id (b1 ++ b2) cs [] in
	   (if e == n then [] -- add b1 ++ b2 if its not yet included by n
	       else [listState c $ getPlainTokenList e]) ++
                   [listState c (b1 ++ [termTok] ++ b2) 
		   , listState c (b1 ++ [termTok, commaTok] ++ b2)]
		   ) $ Set.toList lists

-- these are the possible matches for the nonterminal TERM
-- the same states are used for the predictions  

initialState :: GlobalAnnos -> ([Id], [Id]) -> Int -> [State]
initialState g (ops, preds) i = 
    let mkPredState b toks = State (Id toks [] [], b) [] [] toks i
	mkTokState = mkPredState False
    in concat [mkTokState [parenTok] : 
       mkTokState [termTok, colonTok] :
       mkTokState [termTok, asTok] :
       mkTokState [varTok] :
       mkTokState [opTok] :
       mkTokState [opTok, parenTok] :
       mkPredState True [predTok] :
       mkPredState True [predTok, parenTok] :
       listStates g i, 
       map (mkState i True) preds,
       map (mkApplState i True) preds,
       map (mkState i False) ops,
       map (mkApplState i False) ops]

type ParseMap = Map Int [State]

lookUp :: (Ord a, MonadPlus m) => Map a (m b) -> a -> (m b)
lookUp ce k = findWithDefault mzero k ce

-- match (and shift) a token (or partially finished term)

scan :: TERM -> Int -> ParseMap -> ParseMap
scan trm i m = 
  let t = case trm of 
	  Mixfix_token x -> x
	  Mixfix_sorted_term _ _ -> colonTok
	  Mixfix_cast _ _ -> asTok
          Mixfix_parenthesized _ _ -> parenTok
	  Application (Qual_op_name _ _ _) [] _ -> opTok
          Mixfix_qual_pred _ -> predTok
          _ -> varTok
  in
    Map.insert (i+1) ( 
       foldr (\ (State o b a ts k) l ->
	      if null ts || head ts /= t then l 
	      else let p = tokPos t : b in 
                   if t == commaTok && isListId (fst o) then 
	      -- list elements separator
	             (State o p a 
		      (termTok : commaTok : tail ts) k)
                     : (State o p a (termTok : tail ts) k) : l
              else if t == parenTok then
                     (State o b (trm : a) (tail ts) k) : l
              else if t == varTok || t == opTok || t == predTok then
                     (State o b [trm] (tail ts) k) : l
	      else if t == colonTok || t == asTok then
	             (State o b [mkTerm $ head a] [] k) : l
	           else (State o p a (tail ts) k) : l) [] 
	      (lookUp m i)) m
     where mkTerm t1 = case trm of 
	                  Mixfix_sorted_term s ps -> Sorted_term t1 s ps
	                  Mixfix_cast s ps -> Cast t1 s ps
			  _ -> t1
	      
-- precedence graph stuff

checkArg :: GlobalAnnos -> AssocEither -> Id -> Id -> Bool
checkArg g dir op arg = 
    if arg == op 
       then isAssoc dir (assoc_annos g) op || not (isInfix op)
       else 
       case precRel (prec_annos g) op arg of
       Lower -> True
       NoDirection -> not $ isInfix arg
       _ -> False

checkAnyArg :: GlobalAnnos -> Id -> Id -> Bool
checkAnyArg g op arg = 
    case precRel (prec_annos g) op arg of
    BothDirections -> isInfix op && op == arg
    _ -> True				       

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
filterByPrec :: GlobalAnnos -> State -> State -> Bool
filterByPrec _ _ (State _ _ _ [] _) = False 
filterByPrec g (State (argIde, predArg) _ _ _ _) 
		 (State (opIde, predOp) _ args (hd:_) _) = 
       if hd == termTok then 
	  if predArg
	  then False 
	  else if isListId opIde || isListId argIde || predOp
	       then True else 
	       let n = length args in
		    if isLeftArg opIde n then 
		       if isPostfix opIde && (isPrefix argIde
					      || isInfix argIde) then False
		       else checkArg g ALeft opIde argIde 
		    else if isRightArg opIde n then 
                            if isPrefix opIde && isInfix argIde then False
	                    else checkArg g ARight opIde argIde
                         else checkAnyArg g opIde argIde
       else False

-- constructing the parse tree from (the final) parser state(s)

stateToAppl :: State -> TERM
stateToAppl (State (ide, _) rs a _ _) = 
    let vs = getPlainTokenList ide 
        ar = reverse a
        qs = reverse rs
    in if  vs == [termTok, colonTok] 
	   || vs == [termTok, asTok] 
	   || vs == [varTok] 
           || vs == [opTok]
           || vs == [predTok]
           || vs == [parenTok]
       then case head ar of 
            Mixfix_parenthesized ts _ -> if isSingle ts then head ts
					 else head ar
	    har -> har
       else if vs == [opTok, parenTok]
		 then let Application q _ _ = head ar
                          Mixfix_parenthesized ts ps = head a
                      in Application q ts ps 
		 else if vs == [predTok, parenTok] 
		      then Mixfix_term [head ar, head a] 
                      else case ar of 
		           [Mixfix_parenthesized ts ps] -> 
			       Application (Op_name 
					    (setIdePos ide ts qs))
				ts ps
			   _ -> let newIde@(Id (t:_) _ _) = setIdePos ide ar qs
                                    pos = if isPlace t then posOfTerm $ head ar
					  else tokPos t
			        in Application (Op_name newIde) ar [pos]
				   -- true mixfix

asListAppl :: GlobalAnnos -> State -> TERM
asListAppl g s@(State (i,_) bs a _ _) =
    if isListId i then    
           let Id _ [f] _ = i
	       ListCons b c = getLiteralType g f
	       (b1, _, _) = getListBrackets b
	       cl = length $ getPlainTokenList b
               nb1 = length b1
               ra = reverse a
               na = length ra
               nb = length bs
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null a then asAppl c [] (if null bs then nullPos else last bs)
	      else if nb + 2 == cl + na then
		   let br = reverse bs 
		       br1 = drop (nb1 - 1) br 
	           in  mkList (reverse a) br1  
		   else error "asListAppl"
    else stateToAppl s

-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ k) = 
    map (\ (State o b a ts k1) ->
	 State o b (asListAppl g s : a) 
	 (tail ts) k1)
    $ filter (filterByPrec g s)
    $ lookUp m k

compl :: GlobalAnnos -> ParseMap -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ ts _) -> null ts) l

complRec :: GlobalAnnos -> ParseMap -> [State] -> [State]
complRec g m l = 
    let l1 = compl g m l in 
	if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> ParseMap -> ParseMap
complete g i m = 
    Map.insert i (complRec g m $ lookUp m i) m

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: GlobalAnnos -> [Id] -> Int -> ParseMap -> ParseMap
predict g ops i m = 
    if i /= 0 && any (\ (State _ _ _ ts _) -> not (null ts) 
		      && head ts == termTok) (lookUp m i)
    then insertWith (++) i (initialState g (ops, []) i) m
    else m 

type Chart = (Int, [Diagnosis], ParseMap)

nextState :: GlobalAnnos -> [Id] -> TERM 
	  -> Chart -> Chart
nextState g ops trm (i, ds, m) = 
    let m1 = complete g (i+1) $
		 scan trm i $
		 predict g ops i m
    in if null (lookUp m1 (i+1)) && null ds
		    then (i+1, Diag Error ("unexpected mixfix token: " 
				      ++ showTerm g trm)
			       (posOfTerm trm) : ds, m)
       else (i+1, ds, m1)

type IdSet = (Set Id, Set Id, Set Id)

iterateStates :: GlobalAnnos -> IdSet -> Bool -> [TERM] -> Chart -> Chart
iterateStates g ids@(ops, _, _) maybeFormula terms c@(i, ds, m) = 
    let self = iterateStates g ids maybeFormula
	expand = expandPos Mixfix_token 
	oneStep = nextState g (Set.toList ops)
	resolvePred = resolveMixTrm g ids
        resolveTerm = resolvePred maybeFormula
    in if null terms then c
       else case head terms of
            Mixfix_term ts -> self (ts ++ tail terms) c
            Mixfix_bracketed ts ps -> 
		self (expand ("[", "]") ts ps ++ tail terms) c
	    Mixfix_braced ts ps -> 
		self (expand ("{", "}") ts ps ++ tail terms) c
	    Mixfix_parenthesized ts ps -> 
		let Result mds v = 
			do tsNew <- mapM resolveTerm ts
			   return $ Mixfix_parenthesized tsNew ps
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		in self (tail terms) (oneStep tNew (i, ds++mds, m))
	    Conditional t1 f2 t3 ps -> 
                let Result mds v = 
			do t4 <- resolvePred False t1
			   f5 <- resolveMixFrm g ids f2 		 
			   t6 <- resolvePred False t3 
			   return (Conditional t4 f5 t6 ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		in self (tail terms) (oneStep tNew (i, ds++mds, m)) 
            Mixfix_token t -> let (ds1, trm) = 
				      convertMixfixToken (literal_annos g) t
			      in self (tail terms) 
				     (oneStep trm (i, ds1++ds, m))
	    t ->  self (tail terms) (oneStep t c)


posOfTerm :: TERM -> Pos
posOfTerm trm =
    case trm of
	      Mixfix_token t -> tokPos t
	      Mixfix_term ts -> posOfTerm (head ts)
	      Simple_id i -> tokPos i
	      Mixfix_qual_pred p -> 
		  case p of 
		  Pred_name i -> posOfId i
		  Qual_pred_name _ _ ps -> first (Just ps)
              Application (Qual_op_name _ _ ps) [] [] -> first (Just ps)
	      _ -> first $ get_pos_l trm 
              
    where first ps = case ps of 
		    Nothing -> nullPos
		    Just l -> if null l then nullPos else head l

getAppls :: GlobalAnnos -> Int -> ParseMap -> [TERM]
getAppls g i m = 
    map (asListAppl g) $ 
	filter (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     lookUp m i

mkIdSet :: Set Id -> Set Id -> IdSet
mkIdSet ops preds = 
    let both = Set.intersection ops preds in
	(ops, Set.difference preds both, preds)

resolveMixfix :: GlobalAnnos -> Set Id -> Set Id -> Bool -> TERM -> Result TERM
resolveMixfix g ops preds maybeFormula t = 
    let r@(Result ds _) = resolveMixTrm g (mkIdSet ops preds) maybeFormula t 
	in if null ds then r else Result ds Nothing

resolveMixTrm :: GlobalAnnos -> IdSet -> Bool 
	      -> TERM -> Result TERM
resolveMixTrm g ids@(ops, preds, _) mayBeFormula trm =
    let (i, ds, m) = iterateStates g ids mayBeFormula [trm] 
		     (0, [], Map.single 0 $ initialState g 
		      (Set.toList ops, if mayBeFormula then 
					    Set.toList preds else []) 0)
        ts = getAppls g i m
    in if null ts then if null ds then 
                        plain_error trm ("no resolution for term: "
					     ++ showTerm g trm)
					    (posOfTerm trm)
		       else Result ds (Just trm)
       else if null $ tail ts then Result ds (Just (head ts))
	    else Result (Diag Error ("ambiguous mixfix term\n\t" ++ 
			 (concat  
			 $ intersperse "\n\t" 
			 $ map (showTerm g) 
			 $ take 5 ts)) (posOfTerm trm) : ds) (Just trm)

resolveFormula :: GlobalAnnos -> Set Id -> Set Id -> FORMULA -> Result FORMULA
resolveFormula g ops preds f =     
    let r@(Result ds _) = resolveMixFrm g (mkIdSet ops preds) f 
	in if null ds then r else Result ds Nothing

resolveMixFrm :: GlobalAnnos -> IdSet-> FORMULA -> Result FORMULA
resolveMixFrm g ids@(ops, onlyPreds, preds) frm =
    let self = resolveMixFrm g ids 
	resolveTerm = resolveMixTrm g ids False in
    case frm of 
       Quantification q vs fOld ps -> 
	   let varIds = Set.fromList $ concatMap (\ (Var_decl va _ _) -> 
			       map simpleIdToId va) vs
	       newIds = (Set.union ops varIds,
			 (Set.\\) onlyPreds varIds, preds)
           in   
	   do fNew <- resolveMixFrm g newIds fOld 
	      return $ Quantification q vs fNew ps
       Conjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Conjunction fsNew ps
       Disjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Disjunction fsNew ps
       Implication f1 f2 ps -> 
	   do f3 <- self f1 
	      f4 <- self f2
	      return $ Implication f3 f4 ps
       Equivalence f1 f2 ps -> 
	   do f3 <- self f1 
	      f4 <- self f2
	      return $ Equivalence f3 f4 ps
       Negation fOld ps -> 
	   do fNew <- self fOld  
	      return $ Negation fNew ps
       Predication sym tsOld ps -> 
	   do tsNew <- mapM resolveTerm tsOld  
	      return $ Predication sym tsNew ps
       Definedness tOld ps -> 
	   do tNew <- resolveTerm tOld  
	      return $ Definedness tNew ps
       Existl_equation t1 t2 ps -> 
	   do t3 <- resolveTerm t1 
	      t4 <- resolveTerm t2
	      return $ Existl_equation t3 t4 ps
       Strong_equation t1 t2 ps -> 
	   do t3 <- resolveTerm t1 
	      t4 <- resolveTerm t2
	      return $ Strong_equation t3 t4 ps
       Membership tOld s ps -> 
	   do tNew <- resolveTerm tOld  
	      return $ Membership tNew s ps
       Mixfix_formula tOld -> 
	   do tNew <- resolveMixTrm g ids True tOld
	      mkPredication tNew
         where mkPredication t = 
	         case t of 
		 Mixfix_parenthesized [t0] ps ->
		  do p <- mkPredication t0
		     return $ if null ps then p 
                            else updFormulaPos (head ps) (last ps) p
		 Application (Op_name ide) args ps -> 
		     let p = Predication (Pred_name ide) args ps in
		     if ide `Set.member` preds 
		     then return p else 
			  plain_error p 
		          ("not a predicate: " ++ showId ide "")
			  (posOfTerm t)
		 Mixfix_qual_pred qide ->
		  return $ Predication qide [] []
		 Mixfix_term [Mixfix_qual_pred qide, 
			      Mixfix_parenthesized ts ps] ->
		  return $ Predication qide ts ps
                 Mixfix_term _ -> return $ Mixfix_formula t -- still wrong
		 _ -> plain_error (Mixfix_formula t)
	                ("not a formula: " ++ showTerm g t)
			(posOfTerm t)
       f -> return f


-- --------------------------------------------------------------- 
-- convert literals 
-- --------------------------------------------------------------- 

makeStringTerm :: Id -> Id -> Token -> TERM
makeStringTerm c f tok = 
  makeStrTerm (incSourceColumn sp 1) str
  where 
  sp = tokPos tok
  str = init (tail (tokStr tok))
  makeStrTerm p l = 
    if null l then asAppl c [] p
    else let (hd, tl) = splitString caslChar l
         in asAppl f [asAppl (Id [Token ("'" ++ hd ++ "'") p] [] []) [] p, 
		      makeStrTerm (incSourceColumn p $ length hd) tl] p

makeNumberTerm :: Id -> Token -> TERM
makeNumberTerm f t@(Token n p) =
    case n of
           [] -> error "makeNumberTerm"
	   [_] -> asAppl (Id [t] [] []) [] p
	   hd:tl -> asAppl f [asAppl (Id [Token [hd] p] [] []) [] p, 
			      makeNumberTerm f (Token tl 
						(incSourceColumn p 1))] p

makeFraction :: Id -> Id -> Token -> TERM
makeFraction f d t@(Token s p) = 
    let (n, r) = span (\c -> c /= '.') s
        dotOffset = length n 
    in if null r then makeNumberTerm f t
       else asAppl d [makeNumberTerm f (Token n p),
		      makeNumberTerm f (Token (tail r) 
					(incSourceColumn p $ dotOffset + 1))]
            $ incSourceColumn p dotOffset

makeSignedNumber :: Id -> Token -> TERM
makeSignedNumber f t@(Token n p) = 
  case n of 
  [] -> error "makeSignedNumber"
  hd:tl ->   
    if hd == '-' || hd == '+' then
       asAppl (Id [Token [hd] p] [] []) 
		  [makeNumberTerm f (Token tl $ incSourceColumn p 1)] p
    else makeNumberTerm f t

makeFloatTerm :: Id -> Id -> Id -> Token -> TERM
makeFloatTerm f d e t@(Token s p) = 
    let (m, r) = span (\c -> c /= 'E') s
        offset = length m
    in if null r then makeFraction f d t
       else asAppl e [makeFraction f d (Token m p),
		      makeSignedNumber f (Token (tail r) 
					  $ incSourceColumn p (offset + 1))]
		$ incSourceColumn p offset

asAppl :: Id -> [TERM] -> Pos -> TERM
asAppl f args p = let pos = if null args then [] else [p]
		  in Application (Op_name f) args pos

-- analyse Mixfix_token
convertMixfixToken::  LiteralAnnos -> Token  -> ([Diagnosis], TERM) 
convertMixfixToken ga t = 
     if isString t then 
	case string_lit ga of
	Nothing -> err "string"
        Just (c, f) -> ([], makeStringTerm c f t)
     else if isNumber t then
	  case number_lit ga of
	  Nothing -> err "number"
	  Just f -> if isFloating t then
		        case float_lit ga of
			Nothing -> err "floating"
			Just (d, e) -> ([], makeFloatTerm f d e t)
		    else ([], makeNumberTerm f t)
     else ([], te)
    where te =  Mixfix_token t
          err s = ([Diag Error ("missing %" ++ s ++ " annotation") (tokPos t)]
		  , te)

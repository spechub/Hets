
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
-}

module CASL.MixfixParser ( resolveFormula, resolveMixfix)
    where 
import CASL.AS_Basic_CASL 
import Common.GlobalAnnotations
import Common.Result
import Common.Id
import qualified Common.Lib.Set as Set
import Common.Lexer
import Control.Monad
import Common.Lib.Parsec
import Common.Earley
import CASL.ShowMixfix 
-- import Control.Exception (assert)

type SItem = Item TERM Bool  -- True means predicate

mkSItem :: Index -> Bool -> Id -> SItem 
mkSItem i b ide = mkMixfixItem i (ide,b) 

mkSingleArgSItem :: Index -> Bool -> Id -> SItem
mkSingleArgSItem i b ide = mkItem i ide b 
    (getPlainTokenList ide ++ [varTok])

mkSingleOpArgSItem :: Index -> Bool -> Id -> SItem
mkSingleOpArgSItem i b ide = mkItem i ide b 
    (getPlainTokenList ide ++ [exprTok])

mkArgsSItem :: Index -> Bool -> Id -> SItem
mkArgsSItem i b ide = mkItem i ide b 
    (getPlainTokenList ide ++ getTokenPlaceList tupleId)

singleArgId, singleOpArgId, multiArgsId :: Id
singleArgId = mkRuleId (getPlainTokenList exprId ++ [varTok])
singleOpArgId = mkRuleId (getPlainTokenList exprId ++ [exprTok])

multiArgsId = mkRuleId (getPlainTokenList exprId ++
				 getPlainTokenList tupleId)

-- these are the possible matches for the nonterminal TERM
-- the same states are used for the predictions  

initialSItem :: GlobalAnnos -> ([Id], [Id]) -> Index -> [SItem]
initialSItem g (ops, preds) i = 
    concat [mkSItem i False typeId :
       mkSItem i False exprId :
       mkSItem i False varId :
       mkSItem i False singleArgId :
       mkSItem i False singleOpArgId :
       mkSItem i False multiArgsId :
       listStates False g i, 
       map (mkSItem i True) preds,
       map (mkSingleArgSItem i True) preds,
       map (mkSingleOpArgSItem i True) preds,
       map (mkArgsSItem i True) preds,
       map (mkSItem i False) ops,
       map (mkSingleArgSItem i False) ops,
       map (mkSingleOpArgSItem i False) ops,
       map (mkArgsSItem i False) ops]

-- | meaningful position of a term
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

-- | construct application
asAppl :: Id -> [TERM] -> Pos -> TERM
asAppl f as p = let pos = if null as then [] else [p]
		  in Application (Op_name f) as pos

-- | constructing the parse tree from (the final) parser state(s)
stateToAppl :: SItem -> TERM
stateToAppl st = 
    let ide = rule st 
        ar = reverse $ args st
        qs = reverse $ posList st
    in if  ide == typeId
	   || ide == exprId 
           || ide == parenId
	   || ide == varId
       then assert (isSingle ar) $ head ar
       else if ide == tupleId then  Mixfix_parenthesized ar qs
       else if ide == singleArgId || ide == multiArgsId
	    then assert (length ar > 1) $ 
		 let har:tar = ar
		     ps = posOfTerm har : qs 
		     in case har of
		 Application q ts _ -> assert (null ts) $ 
					Application q tar ps
		 Mixfix_qual_pred _ -> Mixfix_term [har,
				   Mixfix_parenthesized tar ps]
		 _ -> error "stateToAppl"
	    else let newIde@(Id (t:_) _ _) = setIdePos ide ar qs
		     pos = if isPlace t then posOfTerm $ head ar
					  else tokPos t
			        in Application (Op_name newIde) ar [pos]
				   -- true mixfix

asListAppl :: GlobalAnnos -> SItem -> TERM
asListAppl g s =
    let i = rule s
        ra = reverse $ args s
        br = reverse $ posList s in
    if isListId i then    
           let Id _ [f] _ = i
	       ListCons b c = getLiteralType g f
	       (b1, _, _) = getListBrackets b
	       cl = length $ getPlainTokenList b
               nb1 = length b1
               na = length ra
               nb = length br
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null ra then asAppl c [] 
		  (if null br then nullPos else head br)
	      else if nb + 2 == cl + na then
		   let br1 = drop (nb1 - 1) br 
	           in  mkList ra br1  
		   else error "asListAppl"
    else stateToAppl s

type IdSet = (Set.Set Id, Set.Set Id, Set.Set Id)

type Chart = State TERM Bool

addType :: TERM -> TERM -> TERM
addType tt t = 
    case tt of
    Mixfix_sorted_term s ps -> Sorted_term t s ps
    Mixfix_cast s ps -> Cast t s ps
    _ -> error "addType"

initSItems ::  GlobalAnnos -> IdSet -> Bool -> Index -> [SItem]
initSItems ga (ops, preds, _) maybeFormula = 
    initialSItem ga (Set.toList ops,  if maybeFormula then 
		     Set.toList preds else [])

filterByPredicate :: Bool -> Bool -> Maybe Bool
filterByPredicate bArg bOp = 
    if bArg then Just False else
       if bOp then Just True else Nothing

nextStep :: GlobalAnnos -> IdSet -> Bool -> Chart -> (TERM, Token) -> Chart
nextStep ga ids maybeFormula =
    nextState (initSItems ga ids maybeFormula)
    addType Set.empty filterByPredicate (asListAppl ga) ga

iterateStates :: GlobalAnnos -> IdSet -> Bool -> [TERM] -> Chart 
	      -> Chart
iterateStates g ids maybeFormula terms c = 
    let selfcall = iterateStates g ids
	self = selfcall maybeFormula
	selfTerm = selfcall False
	expand = expandPos Mixfix_token 
	oneStep = nextStep g ids maybeFormula c
	resolveTerm = resolveMixTrm g ids False
    in if null terms then c
       else case head terms of
            Mixfix_term ts -> self (ts ++ tail terms) c
            Mixfix_bracketed ts ps -> 
		self (expand ("[", "]") ts ps ++ tail terms) c
	    Mixfix_braced ts ps -> 
		self (expand ("{", "}") ts ps ++ tail terms) c
	    Mixfix_parenthesized ts ps -> 
		if isSingle ts then 
		   let Result mds v = resolveMixTrm g ids maybeFormula
				      $ head ts
		       tNew = case v of Nothing -> head ts
					Just x -> x
		       c2 = selfTerm (tail terms) (oneStep (tNew, varTok))
		   in c2 {solveDiags = mds ++ solveDiags c2 }
		else self (expand ("(", ")") ts ps ++ tail terms) c
	    Conditional t1 f2 t3 ps -> 
                let Result mds v = 
			do t4 <- resolveTerm t1
			   f5 <- resolveMixFrm g ids f2 		 
			   t6 <- resolveTerm t3 
			   return (Conditional t4 f5 t6 ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		    c2 = selfTerm (tail terms) (oneStep (tNew, varTok))
		in c2 {solveDiags = mds ++ solveDiags c2 }
            Mixfix_token t -> let (ds1, trm) = 
				      convertMixfixToken (literal_annos g) t
			          c2 = selfTerm (tail terms) $ oneStep $ 
				       case trm of 
						Mixfix_token tok -> (trm, tok)
						_ -> (trm, varTok)
				  in c2 {solveDiags = ds1 ++ solveDiags c2 }
	    t@(Mixfix_sorted_term _ _) -> selfTerm (tail terms) 
					  (oneStep (t, typeTok))
	    t@(Mixfix_cast _ _) -> selfTerm (tail terms) 
					  (oneStep (t, typeTok))
	    t@(Qual_var _ _ _) -> selfTerm (tail terms) 
					  (oneStep (t, varTok))
	    t ->  selfTerm (tail terms) (oneStep (t, exprTok))

mkIdSet :: Set.Set Id -> Set.Set Id -> IdSet
mkIdSet ops preds = 
    let both = Set.intersection ops preds in
	(ops, Set.difference preds both, preds)

resolveMixfix :: GlobalAnnos -> Set.Set Id -> Set.Set Id -> Bool -> TERM 
	      -> Result TERM
resolveMixfix g ops preds maybeFormula t = 
    let r@(Result ds _) = resolveMixTrm g (mkIdSet ops preds) maybeFormula t 
	in if null ds then r else Result ds Nothing

resolveMixTrm :: GlobalAnnos -> IdSet -> Bool 
	      -> TERM -> Result TERM
resolveMixTrm ga ids maybeFormula trm =
	getResolved showTerm (posOfTerm trm) (asListAppl ga)
	   $ iterateStates ga ids maybeFormula [trm] $ 
	    initState $ initSItems ga ids maybeFormula

resolveFormula :: GlobalAnnos -> Set.Set Id -> Set.Set Id -> FORMULA 
	       -> Result FORMULA
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
		 Application (Op_name ide) as ps -> 
		     let p = Predication (Pred_name ide) as ps in
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
		 _ -> plain_error (Mixfix_formula t)
	                ("not a formula: " ++ showTerm t "")
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




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

assert :: Bool -> a -> a
assert b a = if b then a else error ("assert")

type Rule = (Id, Bool, [Token])  -- True means predicate

mixRule :: Bool -> Id -> Rule
mixRule b ide = (ide, b, getTokenPlaceList ide) 

mkRule :: Id -> Rule
mkRule = mixRule False

mkSingleArgRule :: Bool -> Id -> Rule
mkSingleArgRule b ide = (protect ide, b, getPlainTokenList ide ++ [varTok])

mkSingleOpArgRule :: Bool -> Id -> Rule
mkSingleOpArgRule b ide = (protect ide, b, getPlainTokenList ide ++ [exprTok])

mkArgsRule :: Bool -> Id -> Rule
mkArgsRule b ide = (protect ide, b, getPlainTokenList ide 
		      ++ getTokenPlaceList tupleId)

singleArgId, singleOpArgId, multiArgsId :: Id
singleArgId = mkRuleId (getPlainTokenList exprId ++ [varTok])
singleOpArgId = mkRuleId (getPlainTokenList exprId ++ [exprTok])

multiArgsId = mkRuleId (getPlainTokenList exprId ++
				 getPlainTokenList tupleId)

initRules ::  GlobalAnnos -> IdSet -> Bool -> [Rule]
initRules ga (opS, predS, _) maybeFormula = 
    let ops = Set.toList opS
	preds = if maybeFormula then 
		     Set.toList predS else []
    in concat [ mkRule typeId :
       mkRule exprId :
       mkRule varId :
       mkRule singleArgId :
       mkRule singleOpArgId :
       mkRule multiArgsId :
       listRules False ga, 
       map (mixRule True) preds,
       map (mkSingleArgRule True) preds,
       map (mkSingleOpArgRule True) preds,
       map (mkArgsRule True) preds,
       map mkRule ops,
       map (mkSingleArgRule False) ops,
       map (mkSingleOpArgRule False) ops,
       map (mkArgsRule False) ops]

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
              Application o [] [] -> 
		  case o of 
		  Op_name i ->  posOfId i
		  Qual_op_name _ _ ps -> first (Just ps)
	      _ -> first $ get_pos_l trm 
    where first ps = case ps of 
		    Nothing -> nullPos
		    Just l -> if null l then nullPos else head l

-- | construct application
asAppl :: Id -> [TERM] -> [Pos] -> TERM
asAppl f as ps = Application (Op_name f) as ps

-- | constructing the parse tree from (the final) parser state(s)
toAppl :: Id -> Bool -> [TERM] -> [Pos] -> TERM
toAppl ide _ ar qs = 
       if ide == singleArgId || ide == multiArgsId
	    then assert (length ar > 1) $ 
		 let har:tar = ar
		     ps = posOfTerm har : qs 
		     in case har of
		 Application q ts _ -> assert (null ts) $ 
					Application q tar ps
		 Mixfix_qual_pred _ -> Mixfix_term [har,
				   Mixfix_parenthesized tar ps]
		 _ -> error "stateToAppl"
	    else Application (Op_name ide) ar qs

type IdSet = (Set.Set Id, Set.Set Id, Set.Set Id)

addType :: TERM -> TERM -> TERM
addType tt t = 
    case tt of
    Mixfix_sorted_term s ps -> Sorted_term t s ps
    Mixfix_cast s ps -> Cast t s ps
    _ -> error "addType"


filterByPredicate :: Bool -> Bool -> Maybe Bool
filterByPredicate bArg bOp = 
    if bArg then Just False else
       if bOp then Just True else Nothing

type TermChart = Chart TERM Bool

iterateCharts :: GlobalAnnos -> IdSet -> Bool -> [TERM] -> TermChart 
	      -> TermChart
iterateCharts g ids maybeFormula terms c = 
    let self = iterateCharts g ids maybeFormula
	expand = expandPos Mixfix_token 
	oneStep = nextChart addType filterByPredicate toAppl Set.empty g c
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
		       c2 = self (tail terms) (oneStep (tNew, varTok))
		   in mixDiags mds c2
		else self (expand ("(", ")") ts ps ++ tail terms) c
	    Conditional t1 f2 t3 ps -> 
                let Result mds v = 
			do t4 <- resolveTerm t1
			   f5 <- resolveMixFrm g ids f2 		 
			   t6 <- resolveTerm t3 
			   return (Conditional t4 f5 t6 ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		    c2 = self (tail terms) 
			 (oneStep (tNew, varTok {tokPos = posOfTerm tNew}))
		in mixDiags mds c2
            Mixfix_token t -> let (ds1, trm) = 
				      convertMixfixToken (literal_annos g) t
			          c2 = self (tail terms) $ oneStep $ 
				       case trm of 
						Mixfix_token tok -> (trm, tok)
						_ -> (trm, varTok 
						      {tokPos = tokPos t})
				  in mixDiags ds1 c2
	    t@(Mixfix_sorted_term _ (p:_)) -> self (tail terms) 
			    (oneStep (t, typeTok {tokPos = p}))
	    t@(Mixfix_cast _ (p:_)) -> self (tail terms) 
			    (oneStep (t, typeTok {tokPos = p}))
	    t@(Qual_var _ _ (p:_)) -> self (tail terms) 
			    (oneStep (t, varTok {tokPos = p}))
	    t@(Application (Qual_op_name _ _ (p:_)) _ _) -> 
		self (tail terms) (oneStep (t, exprTok{tokPos = p} ))
	    t@(Mixfix_qual_pred (Qual_pred_name _ _ (p:_))) -> 
		self (tail terms) (oneStep (t, exprTok{tokPos = p} ))
	    t -> error ("iterate mixfix states: " ++ show t)

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
	getResolved showTerm (posOfTerm trm) toAppl
	   $ iterateCharts ga ids maybeFormula [trm] $ 
	    initChart $ initRules ga ids maybeFormula

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
			  (posOfId ide)
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
    if null l then asAppl c [] [p]
    else let (hd, tl) = splitString caslChar l
         in asAppl f [asAppl (Id [Token ("'" ++ hd ++ "'") p] [] []) [] [p], 
		      makeStrTerm (incSourceColumn p $ length hd) tl] [p]

makeNumberTerm :: Id -> Token -> TERM
makeNumberTerm f t@(Token n p) =
    case n of
           [] -> error "makeNumberTerm"
	   [_] -> asAppl (Id [t] [] []) [] [p]
	   hd:tl -> asAppl f [asAppl (Id [Token [hd] p] [] []) [] [p], 
			      makeNumberTerm f (Token tl 
						(incSourceColumn p 1))] [p]

makeFraction :: Id -> Id -> Token -> TERM
makeFraction f d t@(Token s p) = 
    let (n, r) = span (\c -> c /= '.') s
        dotOffset = length n 
    in if null r then makeNumberTerm f t
       else asAppl d [makeNumberTerm f (Token n p),
		      makeNumberTerm f (Token (tail r) 
					(incSourceColumn p $ dotOffset + 1))]
            [incSourceColumn p dotOffset]

makeSignedNumber :: Id -> Token -> TERM
makeSignedNumber f t@(Token n p) = 
  case n of 
  [] -> error "makeSignedNumber"
  hd:tl ->   
    if hd == '-' || hd == '+' then
       asAppl (Id [Token [hd] p] [] []) 
		  [makeNumberTerm f (Token tl $ incSourceColumn p 1)] [p]
    else makeNumberTerm f t

makeFloatTerm :: Id -> Id -> Id -> Token -> TERM
makeFloatTerm f d e t@(Token s p) = 
    let (m, r) = span (\c -> c /= 'E') s
        offset = length m
    in if null r then makeFraction f d t
       else asAppl e [makeFraction f d (Token m p),
		      makeSignedNumber f (Token (tail r) 
					  $ incSourceColumn p (offset + 1))]
		[incSourceColumn p offset]


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



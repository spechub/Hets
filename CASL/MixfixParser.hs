
{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2002-2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

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
import Common.Earley
import Common.ConvertLiteral
import CASL.ShowMixfix 
import Control.Exception (assert)

-- > 0 means predicate
mkRule :: Id -> Rule
mkRule = mixRule 0

mkSingleArgRule :: Int -> Id -> Rule
mkSingleArgRule b ide = (protect ide, b, getPlainTokenList ide ++ [varTok])

mkSingleOpArgRule :: Int -> Id -> Rule
mkSingleOpArgRule b ide = (protect ide, b, getPlainTokenList ide ++ [exprTok])

mkArgsRule :: Int -> Id -> Rule
mkArgsRule b ide = (protect ide, b, getPlainTokenList ide 
		      ++ getTokenPlaceList tupleId)

singleArgId, singleOpArgId, multiArgsId :: Id
singleArgId = mkId (getPlainTokenList exprId ++ [varTok])
singleOpArgId = mkId (getPlainTokenList exprId ++ [exprTok])

multiArgsId = mkId (getPlainTokenList exprId ++
				 getPlainTokenList tupleId)

initRules ::  GlobalAnnos -> IdSet -> [Rule]
initRules ga (opS, predS) = 
    let ops = Set.toList opS
	preds = Set.toList predS
    in concat [ mkRule typeId :
       mkRule exprId :
       mkRule varId :
       mkRule singleArgId :
       mkRule singleOpArgId :
       mkRule multiArgsId :
       listRules 0 ga, 
       map (mixRule 1) preds,
       map (mkSingleArgRule 1) preds,
       map (mkSingleOpArgRule 1) preds,
       map (mkArgsRule 1) preds,
       map mkRule ops,
       map (mkSingleArgRule 0) ops,
       map (mkSingleOpArgRule 0) ops,
       map (mkArgsRule 0) ops]

-- | meaningful position of a term
posOfTerm :: TERM f -> Pos
posOfTerm trm =
    case trm of
	      Mixfix_token t -> tokPos t
	      Mixfix_term ts -> headPos $ map posOfTerm ts
	      Simple_id i -> tokPos i
	      Mixfix_qual_pred p -> 
		  case p of 
		  Pred_name i -> posOfId i
		  Qual_pred_name i _ _ -> posOfId i
              Application o _ _ -> 
		  case o of 
		  Op_name i ->  posOfId i
		  Qual_op_name i _ _ -> posOfId i
	      Qual_var v _ _ -> tokPos v
	      Sorted_term t _ _ -> posOfTerm t
	      Cast  t _ _ -> posOfTerm t
	      Conditional t _ _ _ -> posOfTerm t
	      Unparsed_term _ ps -> headPos ps
	      Mixfix_sorted_term _ ps -> headPos ps
	      Mixfix_cast _ ps -> headPos ps
              Mixfix_parenthesized _ ps -> headPos ps
              Mixfix_bracketed _ ps -> headPos ps
              Mixfix_braced _ ps -> headPos ps

-- | construct application
asAppl :: Id -> [TERM f] -> [Pos] -> TERM f
asAppl f as ps = Application (Op_name f) as ps

-- | constructing the parse tree from (the final) parser state(s)
toAppl :: Id -> [TERM f] -> [Pos] -> TERM f
toAppl ide ar qs = 
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
	    else asAppl ide ar qs

type IdSet = (Set.Set Id, Set.Set Id)

addType :: TERM f -> TERM f -> TERM f
addType tt t = 
    case tt of
    Mixfix_sorted_term s ps -> Sorted_term t s ps
    Mixfix_cast s ps -> Cast t s ps
    _ -> error "addType"


filterByPredicate :: Int -> Int -> Maybe Bool
filterByPredicate bArg bOp = 
    if bArg > 0 then Just False else
       if bOp > 0 then Just True else Nothing

type TermChart f = Chart (TERM f)

iterateCharts :: GlobalAnnos -> IdSet -> [TERM f] -> TermChart f 
	      -> TermChart f
iterateCharts g ids terms c = 
    let self = iterateCharts g ids
	expand = expandPos Mixfix_token 
	oneStep = nextChart addType filterByPredicate toAppl g c
	resolveTerm = resolveMixTrm g ids
    in if null terms then c
       else case head terms of
            Mixfix_term ts -> self (ts ++ tail terms) c
            Mixfix_bracketed ts ps -> 
		self (expand ("[", "]") ts ps ++ tail terms) c
	    Mixfix_braced ts ps -> 
		self (expand ("{", "}") ts ps ++ tail terms) c
	    Mixfix_parenthesized ts ps -> 
		if isSingle ts then 
		   let Result mds v = resolveMixTrm g ids
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
            Mixfix_token t -> let (ds1, trm) = convertMixfixToken 
				     (literal_annos g) asAppl Mixfix_token t
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
	    _ -> error "iterateCharts"

mkIdSet :: Set.Set Id -> Set.Set Id -> IdSet
mkIdSet ops preds = 
    let both = Set.intersection ops preds in
	(ops, Set.difference preds both)

resolveMixfix :: GlobalAnnos -> Set.Set Id -> Set.Set Id -> TERM f 
	      -> Result (TERM f)
resolveMixfix g ops preds t = 
    let r@(Result ds _) = resolveMixTrm g (mkIdSet ops preds) t 
	in if null ds then r else Result ds Nothing

resolveMixTrm :: GlobalAnnos -> IdSet -> TERM f -> Result (TERM f)
resolveMixTrm ga ids trm =
	getResolved showTerm (posOfTerm trm) toAppl
	   $ iterateCharts ga ids [trm] $ 
	    initChart (initRules ga ids) Set.empty

resolveFormula :: GlobalAnnos -> Set.Set Id -> Set.Set Id -> (FORMULA f)
	       -> Result (FORMULA f)
resolveFormula g ops preds f =     
    let r@(Result ds _) = resolveMixFrm g (mkIdSet ops preds) f 
	in if null ds then r else Result ds Nothing

resolveMixFrm :: GlobalAnnos -> IdSet-> FORMULA f -> Result (FORMULA f)
resolveMixFrm g ids@(ops, onlyPreds) frm =
    let self = resolveMixFrm g ids 
	resolveTerm = resolveMixTrm g ids in
    case frm of 
       Quantification q vs fOld ps -> 
	   let varIds = Set.fromList $ concatMap (\ (Var_decl va _ _) -> 
			       map simpleIdToId va) vs
	       newIds = (Set.union ops varIds,
			 (Set.\\) onlyPreds varIds)
           in   
	   do fNew <- resolveMixFrm g newIds fOld 
	      return $ Quantification q vs fNew ps
       Conjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Conjunction fsNew ps
       Disjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Disjunction fsNew ps
       Implication f1 f2 b ps -> 
	   do f3 <- self f1 
	      f4 <- self f2
	      return $ Implication f3 f4 b ps
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
	   do tNew <- resolveMixTrm g ids tOld
	      mkPredication tNew
         where mkPredication t = 
	         case t of 
		 Application (Op_name ide) as ps -> 
		     return $ Predication (Pred_name ide) as ps
		 Mixfix_qual_pred qide ->
		  return $ Predication qide [] []
		 Mixfix_term [Mixfix_qual_pred qide, 
			      Mixfix_parenthesized ts ps] ->
		  return $ Predication qide ts ps
		 _ -> plain_error (Mixfix_formula t)
	                ("not a formula: " ++ showTerm t "")
			(posOfTerm t)
       f -> return f


{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

Mixfix analysis of terms and patterns, type annotations are also analysed

-}

module HasCASL.MixAna where 

import Common.GlobalAnnotations
import Common.Result
import Common.Id
import Common.Keywords
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Earley
import Common.ConvertLiteral
import Common.Lib.State
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Unify 
import Data.Maybe
import Control.Exception(assert)

opKindFilter :: Int -> Int -> Maybe Bool
opKindFilter arg op = 
    if op < arg then Just True
       else if arg < op then Just False 
	    else Nothing

getIdPrec :: PrecMap -> Set.Set Id -> Id -> Int
getIdPrec (pm, r, m) ps i =  Map.findWithDefault 
    (if begPlace i || endPlace i then if Set.member i ps then r else m - 1
     else m + 1) i pm
					 
addType :: Term -> Term -> Term
addType (MixTypeTerm q ty ps) t = TypedTerm t q ty ps 
addType _ _ = error "addType"

type TermChart = Chart Term

-- | find information for qualified operation
findOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> Type -> Maybe OpInfo
findOpId as tm c i ty = listToMaybe $ fst $
			partitionOpId as tm c i $ TypeScheme [] ([] :=> ty) []

iterateCharts :: GlobalAnnos -> [Term] -> TermChart 
	      -> State Env TermChart
iterateCharts ga terms chart = 
    do e <- get
       let self = iterateCharts ga  
	   oneStep = nextChart addType opKindFilter
		     toMixTerm ga chart
	   as = assumps e
	   tm = typeMap e
       if null terms then return chart else 
	  do let t:tt = terms 
		 recurse trm = self tt $ 
		          oneStep (trm, exprTok {tokPos = posOfTerm trm})
             case t of
		    MixfixTerm ts -> self (ts ++ tt) chart
		    MixTypeTerm q typ ps -> do 
		       mTyp <- anaStarType typ
		       case mTyp of 
			   Nothing -> recurse t
			   Just nTyp -> self tt $ oneStep 
					(MixTypeTerm q nTyp ps, 
					 typeTok {tokPos = headPos ps})
		    BracketTerm b ts ps -> self 
		      (expandPos TermToken (getBrackets b) ts ps ++ tt) chart
		    QualVar v typ ps -> do 
		       mTyp <- anaStarType typ
		       case mTyp of 
			   Nothing -> recurse t
			   Just nTyp -> do 
			       let mi = findOpId as tm (counter e) v nTyp
			       case mi of     
			            Nothing -> addDiags [mkDiag Error 
						  "value not found" v]
				    _ -> return ()
			       recurse $ QualVar v nTyp ps
		    QualOp b io@(InstOpId v _ _) 
			       (TypeScheme rs (qs :=> typ) ss) ps -> do 
		       mTyp <- anaStarType typ
		       case mTyp of 
			   Nothing -> recurse t
			   Just nTyp -> do 
		               let mi = findOpId as tm (counter e) v nTyp
			       case mi of     
			            Nothing -> addDiags [mkDiag Error 
						  "value not found" v]
				    _ -> return ()
			       recurse $ QualOp b io 
					(TypeScheme rs (qs :=> nTyp) ss) ps
		    QuantifiedTerm quant decls hd ps -> do 
		       newDs <- mapM anaGenVarDecl decls
		       mt <- resolve ga hd
		       putAssumps as 
		       putTypeMap tm
		       let newT = case mt of Just trm -> trm
					     _ -> hd
		       recurse $ QuantifiedTerm quant (catMaybes newDs) newT ps
		    LambdaTerm decls part hd ps -> do
		       mDecls <- mapM (resolvePattern ga) decls
		       let newDecls = catMaybes mDecls
		       l <- mapM extractBindings newDecls
		       let bs = concatMap snd l
		       checkUniqueVars bs 
		       mapM_ addVarDecl bs
		       mt <- resolve ga hd
		       putAssumps as
		       let newT = case mt of Just trm -> trm
					     _ -> hd
		       recurse $ LambdaTerm (map fst l) part newT ps
		    CaseTerm hd eqs ps -> do 
		       mt <- resolve ga hd 
		       let newT = case mt of Just trm -> trm
					     _ -> hd
		       newEs <- resolveCaseEqs ga eqs
		       recurse $ CaseTerm newT newEs ps 
		    LetTerm b eqs hd ps -> do 
		       newEs <- resolveLetEqs ga eqs 
		       mt <- resolve ga hd 
		       let newT = case mt of Just trm -> trm
					     _ -> hd
		       putAssumps as
		       recurse $ LetTerm b newEs newT ps
		    TermToken tok -> do
			let (ds1, trm) = convertMixfixToken 
					 (literal_annos ga) 
					 ResolvedMixTerm TermToken tok
			addDiags ds1 
			self tt $ oneStep $ 
				       case trm of 
						TermToken _ -> (trm, tok)
						_ -> (trm, exprTok 
						      {tokPos = tokPos tok})
		    _ -> error ("iterCharts: " ++ show t)

-- * equation stuff 
resolveCaseEq :: GlobalAnnos -> ProgEq -> State Env (Maybe ProgEq) 
resolveCaseEq ga (ProgEq p t ps) = 
    do mp <- resolvePattern ga p
       case mp of 
           Nothing -> return Nothing
	   Just np -> do 
	        as <- gets assumps
		(newP, bs) <- extractBindings np
		checkUniqueVars bs
		mapM_ addVarDecl bs
	        mtt <- resolve ga t
		putAssumps as 
		return $ case mtt of 
		    Nothing -> Nothing
	            Just newT -> Just $ ProgEq newP newT ps

resolveCaseEqs :: GlobalAnnos -> [ProgEq] -> State Env [ProgEq]
resolveCaseEqs _ [] = return []
resolveCaseEqs ga (eq:rt) = 
    do mEq <- resolveCaseEq ga eq
       eqs <- resolveCaseEqs ga rt
       return $ case mEq of 
	       Nothing -> eqs
	       Just newEq -> newEq : eqs

resolveLetEqs :: GlobalAnnos -> [ProgEq] -> State Env [ProgEq]
resolveLetEqs _ [] = return []
resolveLetEqs ga (ProgEq pat trm ps : rt) = 
    do mPat <- resolvePattern ga pat
       case mPat of 
	   Nothing -> do resolve ga trm
			 resolveLetEqs ga rt
	   Just nPat -> do 
	       (newPat, bs) <- extractBindings nPat
	       checkUniqueVars bs
	       mapM addVarDecl bs
	       mTrm <- resolve ga trm
	       case mTrm of
	           Nothing -> resolveLetEqs ga rt 
		   Just newTrm -> do 
		       eqs <- resolveLetEqs ga rt 
		       return (ProgEq newPat newTrm ps : eqs)

-- * pattern stuff

-- | extract bindings from a pattern
extractBindings :: Pattern -> State Env (Pattern, [VarDecl])
extractBindings pat = 
    case pat of
    QualVar v t ps -> case t of 
         MixfixType [] -> 
	     do tvar <- toEnvState freshVar
		let ty = TypeName tvar star 1
		return (QualVar v ty ps, [VarDecl v ty Other ps]) 
	 _ -> do mt <- anaStarType t 
		 case mt of 
		     Just ty -> 
			 return (QualVar v ty ps, [VarDecl v ty Other ps]) 
		     _ -> return (pat, [])
    ResolvedMixTerm i pats ps -> do 
         l <- mapM extractBindings pats
	 return (ResolvedMixTerm i (map fst l) ps, concatMap snd l)
    ApplTerm p1 p2 ps -> do
         (p3, l1) <- extractBindings p1
         (p4, l2) <- extractBindings p2
	 return (ApplTerm p3 p4 ps, l1 ++ l2) 
    TupleTerm pats ps -> do 
         l <- mapM extractBindings pats
	 return (TupleTerm (map fst l) ps, concatMap snd l)
    TypedTerm p q ty ps -> do 
         mt <- anaStarType ty 
	 let newT = case mt of Just t -> t
			       _ -> ty
         case p of 
	     QualVar v (MixfixType []) _ ->
		 return (QualVar v newT ps, [VarDecl v newT Other ps])
	     _ -> do (newP, bs) <- extractBindings p
		     return (TypedTerm newP q newT ps, bs)
    AsPattern p1 p2 ps -> do
         (p3, l1) <- extractBindings p1
         (p4, l2) <- extractBindings p2
	 return (AsPattern p3 p4 ps, l1 ++ l2) 
    _ -> return (pat, [])


mkPatAppl :: Pattern -> Pattern -> [Pos] -> Pattern
mkPatAppl op arg qs = 
    case op of
	    QualVar i (MixfixType []) _  -> 
		ResolvedMixTerm i [arg] qs
	    _ -> ApplTerm op arg qs

toMixTerm :: Id -> [Pattern] -> [Pos] -> Pattern
toMixTerm i ar qs = 
    if i == applId then assert (length ar == 2) $
	   let [op, arg] = ar in mkPatAppl op arg qs
    else if i == tupleId || i == unitId then
         mkTupleTerm ar qs
    else if isUnknownId i then
         QualVar (simpleIdToId $ unToken i) 
		     (MixfixType []) qs
    else ResolvedMixTerm i ar qs

getKnowns :: Id -> Knowns
getKnowns (Id ts cs _) = Set.union (Set.fromList (map tokStr ts)) $ 
			 Set.unions (map getKnowns cs) 

resolvePattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
resolvePattern ga = resolver ga (unknownId : builtinIds)

resolve :: GlobalAnnos -> Term -> State Env (Maybe Term)
resolve ga = resolver ga builtinIds

resolver :: GlobalAnnos -> [Id] -> Term 
	 -> State Env (Maybe Term)
resolver ga bs trm =
    do as <- gets assumps
       ps@((_, _, m), _) <- gets preIds
       let ids = Map.keys as
           ks = Set.union (Set.fromList (tokStr exprTok: inS :
					 map (:[]) ":{}[](),"))
		    $ Set.unions $ map getKnowns ids
       chart<- iterateCharts ga [trm] $ 
	       initChart (listRules (m+2) ga ++ 
			  (initRules ps bs 
			  ids)) (if unknownId `elem` bs then ks else Set.empty)
       let Result ds mr = getResolved showPretty (posOfTerm trm) 
			  toMixTerm chart
       addDiags ds
       return mr

builtinIds :: [Id]
builtinIds = [unitId, parenId, tupleId, exprId, typeId, applId]

initRules ::  (PrecMap, Set.Set Id) -> [Id] -> [Id] -> [Rule]
initRules (pm@(_, _, m), ps) bs is = 
    map ( \ i -> mixRule (getIdPrec pm ps i) i) 
	    (bs ++ is) ++
    map ( \ i -> (protect i, m + 2, getPlainTokenList i)) 
	    (filter isMixfix is)

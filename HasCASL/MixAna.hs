
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

Mixfix analysis of terms and patterns, types annotations are also analysed

-}

module HasCASL.MixAna where 

import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Result
import Common.Id
import Common.PrettyPrint
import Common.Keywords
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Earley
import Common.ConvertLiteral
import Common.Lib.State
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Unify 
import HasCASL.TypeAna
import Data.Maybe

-- import Debug.Trace
-- import Control.Exception(assert)
assert :: Bool -> a -> a
assert b a = if b then a else error ("assert")

type Rule = (Id, (), [Token])

trueId :: Id
trueId = mkId [mkSimpleId trueS]

falseId :: Id
falseId = mkId [mkSimpleId falseS]

ifThenElse :: Id
ifThenElse = mkId (map mkSimpleId [ifS, place, thenS, place, elseS, place])

whenElse :: Id
whenElse = mkId (map mkSimpleId [place, whenS, place, elseS, place])

mkInfix :: String -> Id
mkInfix s = mkId $ map mkSimpleId [place, s, place]

infixIf :: Id 
infixIf = mkInfix ifS

exEq :: Id 
exEq = mkInfix exEqual

eqId :: Id 
eqId = mkInfix equalS

andId :: Id 
andId = mkInfix lAnd

orId :: Id 
orId = mkInfix lOr

implId :: Id 
implId = mkInfix implS

eqvId :: Id 
eqvId = mkInfix equivS

defId :: Id 
defId = mkId $ map mkSimpleId [defS, place]

notId :: Id 
notId = mkId $ map mkSimpleId [notS, place]

builtinRelIds :: Set.Set Id 
builtinRelIds = Set.fromDistinctAscList [typeId, eqId, exEq, defId]

addBuiltins :: GlobalAnnos -> Set.Set Id -> Set.Set Id -> GlobalAnnos
addBuiltins ga opIds predIds = 
    let ass = assoc_annos ga
	newAss = Map.union ass $ Map.fromList 
		 [(applId, ALeft), (andId, ALeft), (orId, ALeft), 
		  (implId, ARight), (infixIf, ALeft), 
		  (whenElse, ARight)]
	precs = prec_annos ga
	logIds = Set.fromDistinctAscList 
		 [andId, eqvId, implId, orId, infixIf, notId] 
	relIds = (Set.filter isInfix predIds Set.\\ logIds) `Set.union` 
		 builtinRelIds
	opIs = Set.toList ((((Set.filter isInfix opIds)
		Set.\\ relIds) Set.\\ logIds) 
	        Set.\\ Set.fromDistinctAscList [applId, whenElse])

	logs = [(eqvId, implId), (implId, andId), (implId, orId), 
		(eqvId, infixIf), (infixIf, andId), (infixIf, orId),
		 (andId, notId), (orId, notId)]

        rels1 = map ( \ i -> (notId, i)) $ Set.toList relIds
	rels2 = map ( \ i -> (i, whenElse)) $ Set.toList relIds
	ops1 = map ( \ i -> (whenElse, i)) (applId : opIs)
	ops2 = map ( \ i -> (i, applId)) (whenElse : opIs)
	newPrecs = foldr (\ (a, b) p -> if Rel.member b a p then p else 
			 Rel.insert a b p) precs $  
		  concat [logs, rels1, rels2, ops1, ops2]
    in ga { assoc_annos = newAss
	  , prec_annos = Rel.transClosure newPrecs }

initTermRules :: Set.Set Id -> [Rule]
initTermRules is = map (mixRule ()) (Set.toList
    (Set.fromDistinctAscList 
     [unitId, parenId, tupleId, exprId, typeId, applId] 
     `Set.union` is)) ++
    map ( \ i -> (protect i, (), getPlainTokenList i )) 
	    (filter isMixfix $ Set.toList is)

addType :: Term -> Term -> Term
addType (TypedTerm _ qual ty ps) t = TypedTerm t qual ty ps 
addType (MixInTerm ty ps) t = TypedTerm t InType ty ps 
addType _ _ = error "addType"

dummyFilter :: () -> () -> Maybe Bool
dummyFilter () () = Nothing

toMixTerm :: Id -> () -> [Term] -> [Pos] -> Term
toMixTerm ide _ ar qs = 
    if ide == applId then assert (length ar == 2) $
       let [op, arg] = ar in ApplTerm op arg qs
    else if ide == tupleId || ide == unitId then
	 mkTupleTerm ar qs
    else ResolvedMixTerm ide ar qs

type TermChart = Chart Term ()

-- | find information for qualified operation
findOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> Type -> Maybe OpInfo
findOpId as tm c i ty = listToMaybe $ fst $
			partitionOpId as tm c i $ TypeScheme [] ([] :=> ty) []

iterateCharts :: GlobalAnnos -> [Term] -> TermChart 
	      -> State Env TermChart
iterateCharts ga terms chart = 
    do e <- get
       let self = iterateCharts ga  
	   oneStep = nextChart addType dummyFilter toMixTerm ga chart
	   as = assumps e
	   tm = typeMap e
       if null terms then return chart else 
	  do let t:tt = terms 
		 recurse trm = self tt $ 
		          oneStep (trm, exprTok {tokPos = posOfTerm trm})
             case t of
		    MixfixTerm ts -> self (ts ++ tt) chart
		    MixInTerm _ ps -> self tt $ oneStep (t, 
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
		    TypedTerm hd tqual typ ps -> do
		       mTyp <- anaStarType typ
		       case mTyp of 
		           Nothing -> recurse t
			   Just nTyp -> do 
		               mt <- resolve ga hd 
		               let newT = case mt of Just trm -> trm
						     _ -> hd
			       recurse $ TypedTerm newT tqual nTyp ps
		    QuantifiedTerm quant decls hd ps -> do 
		       newDs <- mapM anaGenVarDecl decls
		       mt <- resolve ga hd
		       putAssumps as 
		       putTypeMap tm
		       let newT = case mt of Just trm -> trm
					     _ -> hd
		       recurse $ QuantifiedTerm quant (catMaybes newDs) newT ps
		    LambdaTerm decls part hd ps -> do
		       mDecls <- mapM (resolveConstrPattern ga) decls
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

resolve :: GlobalAnnos -> Term -> State Env (Maybe Term)
resolve ga trm =
    do as <- gets assumps
       chart<- iterateCharts ga [trm] $ 
	       initChart (initTermRules $ Set.fromDistinctAscList 
			  $ Map.keys as) Set.empty
       let Result ds mr = getResolved showPretty (posOfTerm trm) 
			  toMixTerm chart
       addDiags ds
       return mr

-- * equation stuff 
resolveCaseEq :: GlobalAnnos -> ProgEq -> State Env (Maybe ProgEq) 
resolveCaseEq ga (ProgEq p t ps) = 
    do mp <- resolveConstrPattern ga p
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
    do mPat <- resolveConstrPattern ga pat
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
    PatternVar l@(VarDecl v t sk ps) -> case t of 
         MixfixType [] -> 
	     do tvar <- toEnvState freshVar
		let ty = TypeName tvar star 1
		    vd = VarDecl v ty sk ps
		return (PatternVar vd, [vd]) 
	 _ -> do mt <- anaStarType t 
		 case mt of 
		     Just ty -> do 
		         let vd = VarDecl v ty sk ps
			 return (PatternVar vd, [vd]) 
		     _ -> return (pat, [l])
--    PatternConstr _ _ _ -> return (pat, [])
    ResolvedMixPattern i pats ps -> do 
         l <- mapM extractBindings pats
	 return (ResolvedMixPattern i (map fst l) ps, concatMap snd l)
    ApplPattern p1 p2 ps -> do
         (p3, l1) <- extractBindings p1
         (p4, l2) <- extractBindings p2
	 return (ApplPattern p3 p4 ps, l1 ++ l2) 
    TuplePattern pats ps -> do 
         l <- mapM extractBindings pats
	 return (mkTuplePattern (map fst l) ps, concatMap snd l)
    TypedPattern p ty ps -> do 
         mt <- anaStarType ty 
	 let newT = case mt of Just t -> t
			       _ -> ty
         case p of 
	     PatternVar (VarDecl v (MixfixType []) sk _) -> do 
	         let vd = VarDecl v newT sk ps
		 return (PatternVar vd, [vd])
	     _ -> do (newP, bs) <- extractBindings p
		     return (TypedPattern newP newT ps, bs)
    AsPattern p1 p2 ps -> do
         (p3, l1) <- extractBindings p1
         (p4, l2) <- extractBindings p2
	 return (AsPattern p3 p4 ps, l1 ++ l2) 
    _ -> return (pat, [])
--     _ -> error ("extractBindings: " ++ show pat)


resolveConstrPattern :: GlobalAnnos -> Pattern
		     -> State Env (Maybe Pattern)
resolveConstrPattern ga pat = 
    do as <- gets assumps
       let newAs = filterAssumps ( \ o -> case opDefn o of
					      ConstructData _ -> True
					      VarDefn -> True
					      _ -> False) as
       putAssumps newAs
       mp <- resolvePattern ga pat
       putAssumps as
       return mp

initPatternRules :: [Id] -> [Rule]
initPatternRules is = 
    (tupleId, (), getTokenPlaceList tupleId) :
    (parenId, (), getTokenPlaceList parenId) :
    (unknownId, (), getTokenPlaceList unknownId) : 
    (applId, (), getTokenPlaceList applId) : 
    (exprId, (), getTokenPlaceList exprId) :
    map ( \ i -> (i, (), getTokenPlaceList i )) is ++
    map ( \ i -> (protect i, (), getPlainTokenList i )) (filter isMixfix is)

addPatternType :: Pattern -> Pattern -> Pattern
addPatternType (TypedPattern _ ty ps) p = TypedPattern p ty ps 
addPatternType _ _ = error "addPatternType"


mkPatAppl :: Pattern -> Pattern -> [Pos] -> Pattern
mkPatAppl op arg qs = 
    case op of
	    ResolvedMixPattern i as ps -> 
		ResolvedMixPattern i (as++[arg]) (ps++qs)
	    PatternVar (VarDecl i (MixfixType []) _ _) -> 
		ResolvedMixPattern i [arg] qs
	    TypedPattern p ty ps -> 
		TypedPattern (mkPatAppl p arg qs) ty ps
	    _ -> error ("mkPatAppl: " ++ show op)

toPat :: Id -> () -> [Pattern] -> [Pos] -> Pattern
toPat i _ ar qs = 
    if i == applId then assert (length ar == 2) $
	   let [op, arg] = ar in mkPatAppl op arg qs
    else if i == tupleId then
         mkTuplePattern ar qs
    else if isUnknownId i then
         PatternVar (VarDecl (simpleIdToId $ unToken i) 
		     (MixfixType []) Other qs)
    else ResolvedMixPattern i 
	     (if null ar then [] 
	     else if isSingle ar then [head ar] 
	     else [mkTuplePattern ar qs]) qs

type PatChart = Chart Pattern ()

iterPatCharts :: GlobalAnnos -> [Pattern] -> PatChart -> State Env PatChart
iterPatCharts ga pats chart= 
    let self = iterPatCharts ga
	oneStep = nextChart addPatternType dummyFilter toPat ga chart
    in if null pats then return chart
       else 
       do let p:pp = pats
	      recurse pt = self pp $ 
			   oneStep (pt, exprTok {tokPos = posOfPat pt})
          case p of
		 MixfixPattern ps -> self (ps ++ pp) chart
		 BracketPattern b ps qs -> self 
		   (expandPos PatternToken (getBrackets b) ps qs ++ pp) chart
		 TypedPattern hd typ ps -> do  
		   mp <- resolvePattern ga hd 
		   let np = case mp of Just pt -> pt
				       _ -> p
		   recurse $ TypedPattern np typ ps
		 PatternToken tok -> self pp $ oneStep (p, tok)
		 _ -> error ("iterPatCharts: " ++ show p) 

getKnowns :: Id -> Knowns
getKnowns (Id ts cs _) = Set.union (Set.fromList (map tokStr ts)) $ 
			 Set.unions (map getKnowns cs) 

resolvePattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
resolvePattern ga pat =
    do as <- gets assumps
       let ids = Map.keys as 
	   ks = Set.union (Set.fromList (tokStr exprTok: inS : 
					 map (:[]) "{}[](),"))
		    $ Set.unions $ map getKnowns ids
       chart <- iterPatCharts ga [pat] $ initChart (initPatternRules ids) ks
       let Result ds mp =  getResolved showPretty (posOfPat pat) toPat chart
       addDiags ds
       return mp


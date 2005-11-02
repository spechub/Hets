{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

Mixfix analysis of terms and patterns, type annotations are also analysed
-}

module HasCASL.MixAna where

import Common.GlobalAnnotations
import Common.Result
import Common.Id
import Common.Keywords
import Common.Earley
import Common.ConvertLiteral
import Common.Lib.State
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.Unify
import HasCASL.VarDecl
import HasCASL.Le

import Data.Maybe
import Control.Exception(assert)

getIdPrec :: PrecMap -> Set.Set Id -> Id -> Int
getIdPrec (pm, r, m) ps i =  if i == applId then m + 1
    else Map.findWithDefault
    (if begPlace i || endPlace i then if Set.member i ps then r else m
     else m + 2) i pm

addType :: Term -> Term -> Term
addType (MixTypeTerm q ty ps) t = TypedTerm t q ty ps
addType _ _ = error "addType"

type TermChart = Chart Term

iterateCharts :: GlobalAnnos -> [Term] -> TermChart
              -> State Env TermChart
iterateCharts ga terms chart =
    do e <- get
       let self = iterateCharts ga
           oneStep = nextChart addType toMixTerm (const []) ga chart
           vs = localVars e
           tm = typeMap e
       case terms of
         [] -> return chart
         t:tt -> do
             let recurse trm = self tt $
                          oneStep (trm, exprTok {tokPos = getRange trm})
             case t of
                    MixfixTerm ts -> self (ts ++ tt) chart
                    MixTypeTerm q typ ps -> do
                       mTyp <- anaStarType typ
                       case mTyp of
                           Nothing -> recurse t
                           Just nTyp -> self tt $ oneStep
                                        (MixTypeTerm q (monoType nTyp) ps,
                                         typeTok {tokPos = ps})
                    BracketTerm b ts ps -> self
                      (expandPos TermToken (getBrackets b) ts ps ++ tt) chart
                    QualVar (VarDecl v typ ok ps) -> do
                       mTyp <- anaStarType typ
                       case mTyp of
                           Nothing -> recurse t
                           Just nType -> recurse $ QualVar $
                                         VarDecl v (monoType nType) ok ps
                    QualOp b (InstOpId v ts qs) sc ps -> do
                       mSc <- anaTypeScheme sc
                       newTs <- anaInstTypes ts
                       case mSc of
                           Nothing -> recurse t
                           Just nSc -> do
                               case findOpId e v nSc of
                                    Nothing -> addDiags [mkDiag Error
                                                   "operation not found" v]
                                    _ -> return ()
                               recurse $ QualOp b (InstOpId v newTs qs) nSc ps
                    QuantifiedTerm quant decls hd ps -> do
                       newDs <- mapM (anaddGenVarDecl False) decls
                       mt <- resolve ga hd
                       putLocalVars vs
                       putTypeMap tm
                       let newT = case mt of Just trm -> trm
                                             _ -> hd
                       recurse $ QuantifiedTerm quant (catMaybes newDs) newT ps
                    LambdaTerm decls part hd ps -> do
                       mDecls <- mapM (resolvePattern ga) decls
                       let anaDecls = catMaybes mDecls
                           bs = concatMap extractVars anaDecls
                       checkUniqueVars bs
                       mapM_ (addLocalVar False) bs
                       mt <- resolve ga hd
                       putLocalVars vs
                       recurse $ LambdaTerm anaDecls part (maybe hd id mt) ps
                    CaseTerm hd eqs ps -> do
                       mt <- resolve ga hd
                       newEs <- resolveCaseEqs ga eqs
                       recurse $ CaseTerm (maybe hd id mt) newEs ps
                    LetTerm b eqs hd ps -> do
                       newEs <- resolveLetEqs ga eqs
                       mt <- resolve ga hd
                       putLocalVars vs
                       recurse $ LetTerm b newEs (maybe hd id mt) ps
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
                    AsPattern vd p ps -> do
                        mp <- resolvePattern ga p
                        let newP = case mp of Just pat -> pat
                                              Nothing -> p
                        recurse $ AsPattern vd newP ps
                    TypedTerm trm k ty ps -> do
                        -- assume that type is analysed
                        mt <- resolve ga trm
                        recurse $ TypedTerm (maybe trm id mt) k ty ps
                    _ -> error ("iterCharts: " ++ show t)

-- * equation stuff
resolveCaseEq :: GlobalAnnos -> ProgEq -> State Env (Maybe ProgEq)
resolveCaseEq ga (ProgEq p t ps) =
    do mp <- resolvePattern ga p
       case mp of
           Nothing -> return Nothing
           Just newP -> do
                let bs = extractVars newP
                checkUniqueVars bs
                vs <- gets localVars
                mapM_ (addLocalVar False) bs
                mtt <- resolve ga t
                putLocalVars vs
                return $ case mtt of
                    Nothing -> Nothing
                    Just newT -> Just $ ProgEq newP newT ps

resolveCaseEqs :: GlobalAnnos -> [ProgEq] -> State Env [ProgEq]
resolveCaseEqs _ [] = return []
resolveCaseEqs ga (eq : rt) =
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
           Just newPat -> do
               let bs = extractVars newPat
               checkUniqueVars bs
               mapM_ (addLocalVar False) bs
               mTrm <- resolve ga trm
               case mTrm of
                   Nothing -> resolveLetEqs ga rt
                   Just newTrm -> do
                       eqs <- resolveLetEqs ga rt
                       return (ProgEq newPat newTrm ps : eqs)

mkPatAppl :: Term -> Term -> Range -> Term
mkPatAppl op arg qs =
    case op of
            QualVar (VarDecl i (MixfixType []) _ _) ->
                ResolvedMixTerm i [arg] qs
            _ -> ApplTerm op arg qs

toMixTerm :: Id -> [Term] -> Range -> Term
toMixTerm i ar qs =
    if i == applId then assert (length ar == 2) $
           let [op, arg] = ar in mkPatAppl op arg qs
    else if i == tupleId || i == unitId then
         mkTupleTerm ar qs
    else if isUnknownId i then
         QualVar $ VarDecl (simpleIdToId $ unToken i)
                     (MixfixType []) Other qs
    else ResolvedMixTerm i ar qs

getKnowns :: Id -> Knowns
getKnowns (Id ts cs _) = Set.union (Set.fromList (map tokStr ts)) $
                         Set.unions (map getKnowns cs)

resolvePattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
resolvePattern ga p = do
    mp <- resolver ga (unknownId : builtinIds) p
    case mp of
        Nothing -> return Nothing
        Just np -> fmap Just $ anaPattern np

resolve :: GlobalAnnos -> Term -> State Env (Maybe Term)
resolve ga = resolver ga builtinIds

resolver :: GlobalAnnos -> [Id] -> Term
         -> State Env (Maybe Term)
resolver ga bs trm =
    do ass <- gets assumps
       vs <- gets localVars
       ps@((_, _, m), _) <- gets preIds
       let ids = Set.toList $ Set.union (Rel.keysSet ass) $ Rel.keysSet vs
           ks = Set.union (Set.fromList (tokStr exprTok: inS :
                                         map (:[]) ":{}[](),"))
                    $ Set.unions $ map getKnowns ids
       chart<- iterateCharts ga [trm] $
               initChart (listRules (m + 3) ga ++
                          (initRules ps bs
                          ids)) (if unknownId `elem` bs then ks else Set.empty)
       let Result ds mr = getResolved
              (shows . printTerm emptyGlobalAnnos . parenTerm) (getRange trm)
                          toMixTerm chart
       addDiags ds
       return mr

builtinIds :: [Id]
builtinIds = [unitId, parenId, tupleId, exprId, typeId, applId]

initRules ::  (PrecMap, Set.Set Id) -> [Id] -> [Id] -> [Rule]
initRules (pm@(_, _, m), ps) bs is =
    map ( \ i -> mixRule (getIdPrec pm ps i) i)
            (bs ++ is) ++
    map ( \ i -> (protect i, m + 3, getPlainTokenList i))
            (filter isMixfix is)

-- create fresh type vars for unknown ids tagged with type MixfixType [].
anaPattern :: Pattern -> State Env Pattern
anaPattern pat =
    case pat of
    QualVar vd -> do newVd <- checkVarDecl vd
                     return $ QualVar newVd
    ResolvedMixTerm i pats ps -> do
         l <- mapM anaPattern pats
         return $ ResolvedMixTerm i l ps
    ApplTerm p1 p2 ps -> do
         p3 <- anaPattern p1
         p4 <- anaPattern p2
         return $ ApplTerm p3 p4 ps
    TupleTerm pats ps -> do
         l <- mapM anaPattern pats
         return $ TupleTerm l ps
    TypedTerm p q ty ps -> do
         case p of
             QualVar (VarDecl v (MixfixType []) ok qs) ->
                 let newVd = VarDecl v ty ok (qs `appRange` ps) in
                 return $ QualVar newVd
             _ -> do newP <- anaPattern p
                     return $ TypedTerm newP q ty ps
    AsPattern vd p2 ps -> do
         newVd <- checkVarDecl vd
         p4 <- anaPattern p2
         return $ AsPattern newVd p4 ps
    _ -> return pat
    where checkVarDecl vd@(VarDecl v t ok ps) = case t of
            MixfixType [] -> do
                (tvar, c) <- toEnvState $ freshVar $ posOfId v
                return $ VarDecl v (TypeName tvar rStar c) ok ps
            _ -> return vd

-- | put parenthesis around applications
parenTerm :: Term -> Term
parenTerm trm = case trm of
    ResolvedMixTerm n ts ps ->
        ResolvedMixTerm n (map parenTerm ts) ps
    ApplTerm t1 t2' ps -> let t2 = parenTerm t2' in
        ApplTerm (addParAppl t1) (case t2 of
           ResolvedMixTerm _ [] _ -> t2
           QualVar _ -> t2
           QualOp _ _ _ _ -> t2
           TermToken _ -> t1
           BracketTerm _ _ _ -> t2
           TupleTerm _ _ -> t2
           _ -> addPar t2) ps
    TupleTerm ts ps -> TupleTerm (map parenTerm ts) ps
    TypedTerm t q typ ps ->
        TypedTerm (addParAppl t) q typ ps
    QuantifiedTerm q vs t ps -> QuantifiedTerm q vs (parenTerm t) ps
    LambdaTerm ps q t qs ->
        LambdaTerm (map parenTerm ps) q (parenTerm t) qs
    CaseTerm t es ps -> CaseTerm (parenTerm t) (map parenProgEq es) ps
    LetTerm br es t ps ->
        LetTerm br (map parenProgEq es) (parenTerm t) ps
    MixfixTerm ts -> MixfixTerm $ map addParAppl ts
    BracketTerm k ts ps -> BracketTerm k (map parenTerm ts) ps
    AsPattern v p ps -> AsPattern v (addParAppl p) ps
    TermToken _ -> trm
    MixTypeTerm _ _ _ -> trm
    QualVar _ -> trm
    QualOp _ _ _ _ -> trm
    where addPar t = TupleTerm [t] nullRange
          addParAppl t' = let t = parenTerm t' in case t of
           ApplTerm _ _ _ -> t
           ResolvedMixTerm _ _ _ -> t
           QualVar _ -> t
           QualOp _ _ _ _ -> t
           TermToken _ -> t
           BracketTerm _ _ _ -> t
           TupleTerm _ _ -> t
           _ -> addPar t

-- | put parenthesis around applications in equations
parenProgEq :: ProgEq -> ProgEq
parenProgEq (ProgEq p t q) = ProgEq (parenTerm p) (parenTerm t) q

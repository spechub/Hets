
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

type inference 

-}

module HasCASL.TypeCheck where

import HasCASL.Unify 
import HasCASL.AsUtils
import HasCASL.Merge
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.Le
import HasCASL.MixAna
import HasCASL.MapTerm
import HasCASL.TypeAna
import HasCASL.Constrain
import HasCASL.MinType

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.Lib.State
import Data.Maybe

substTerm :: Subst -> Term -> Term
substTerm s = mapTerm (id, subst s)

resolveTerm :: GlobalAnnos -> Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm ga mt trm = do
    mtrm <- resolve ga trm
    case mtrm of 
              Nothing -> return Nothing
              Just t -> typeCheck mt t 

checkPattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
checkPattern ga pat = do
    mPat <- resolvePattern ga pat
    case mPat of 
              Nothing -> return Nothing
              Just p -> do 
                  np <- anaPattern p 
                  typeCheck Nothing np

instantiate :: TypeScheme -> State Env (Type, [Type], Constraints)
instantiate sc = do
     (typ, inst) <- toEnvState $ freshInstList sc
     return (typ, inst, Set.fromList $ map ( \ ty@(TypeName _ k _)
                                     -> Kinding ty k) inst)

instOpInfo :: OpInfo -> State Env (Type, [Type], Constraints, OpInfo)
instOpInfo oi = do
     (ty, inst, cs) <- instantiate $ opType oi
     return (ty, inst, cs, oi)

lookupError :: Type -> [OpInfo] -> String
lookupError ty ois = 
    "  with (maximal) type: " ++  showPretty ty "\n"
    ++ "  known types:\n    " ++
       showSepList ("\n    "++) (showPretty . opType) ois "" 

checkList :: [Maybe Type] -> [Term] 
          -> State Env [(Subst, Constraints, [Type], [Term])]
checkList [] [] = return [(eps, noC, [], [])]
checkList (ty : rty) (trm : rt) = do 
      fts <- infer ty trm >>= reduce False 
      combs <- mapM ( \ (sf, cs, tyf, tf) -> do
                      rts <- checkList (map (fmap (subst sf)) rty) rt
                      return $ map ( \ (sr, cr, tys, tts) ->
                             (compSubst sf sr, 
                              substC sr cs `joinC` cr,
                              subst sr tyf : tys,
                                     tf : tts)) rts) fts
      return $ concat combs
checkList _ _ = error "checkList"

reduce :: Bool -> [(Subst, Constraints, Type, Term)] 
       -> State Env [(Subst, Constraints, Type, Term)]
reduce b alts = do
       tm <- gets typeMap
       combs <- mapM ( \ (s, cr, ty, tr) -> do 
           Result ds mc <- toEnvState $ preClose tm $ substC s cr
           addDiags $ map (improveDiag tr) ds 
           return $ case mc of 
               Nothing -> []
               Just (cs, cc) -> let 
                   s1 = compSubst s cs
                   ms = if b then monoSubsts tm 
                       (foldr (uncurry Rel.insert) 
                                       (fromTypeMap tm) 
                                        $ toListC cc) (subst s1 ty)
                       else eps
                   s2 = compSubst s1 ms 
                   in [(s2, substC ms cc, subst s2 ty, 
                                     substTerm s2 tr)]) alts
       return $ concat combs

typeCheck :: Maybe Type -> Term -> State Env (Maybe Term)
typeCheck mt trm = 
    do alts <- infer mt trm >>= reduce True 
       tm <- gets typeMap
       let p = getMyPos trm
       if null alts then 
          do addDiags [mkDiag Error "no typing for" trm]
             return Nothing
          else if null $ tail alts then do
               let (_, cs, ty, t) = head alts
                   (ds, rcs) = simplify tm cs 
                   es = map ( \ d -> d {diagKind = Hint, diagPos = p}) ds
               addDiags es 
               if Set.isEmpty rcs then return ()
                  else addDiags [(mkDiag Error ("in term'"
                             ++ showPretty t "' of type '" 
                             ++ showPretty ty "'\n unresolved constraints")
                                 rcs){diagPos = p}]
               return $ Just t
          else let alts3 = filter ( \ (_, cs, _, _) -> 
                             Set.isEmpty $ snd $ simplify tm cs) alts 
                   falts = typeNub tm q2p alts3 in
               if null falts then do
                  addDiags [mkDiag Error "no constraint resolution for" trm]
                  addDiags $ map (\ (_, cs, _, _) -> (mkDiag Hint
                            "simplification failed for" cs){diagPos = p}) alts
                  return Nothing
               else if null $ tail falts then
                    let (_, _, _, t) = head falts in
                    return $ Just t
                    else 
                    do addDiags [Diag Error 
                         ("ambiguous typings \n " ++
                          showSepList ("\n " ++) 
                          ( \ (n, t) -> shows n . (". " ++) . showPretty t)
                          (zip [1..(5::Int)] $ map ( \ (_,_,_,t) -> 
                                          t) falts) "")
                            p]
                       return Nothing

freshTypeVar :: Pos -> State Env Type             
freshTypeVar p = 
    do (var, c) <- toEnvState $ freshVar p
       return $ TypeName var star c

freshVars :: [Term] -> State Env [Type]
freshVars l = mapM (freshTypeVar . posOfTerm) l

inferAppl :: [Pos] -> Maybe Type -> Term  -> Term 
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl ps mt t1 t2 = do
            let origAppl = ApplTerm t1 t2 ps
            aty <- freshTypeVar $ posOfTerm t2
            rty <- case mt of 
                Nothing -> freshTypeVar $ posOfTerm t1
                Just ty -> return ty
            ops <- infer (Just $ FunType aty PFunArr rty []) t1 
                   >>= reduce False
            combs <- mapM ( \ (sf, cf, _, tf) -> do 
                let sfty = subst sf aty
                args <- infer (Just sfty) t2 >>= reduce False
--                   args2 <- infer (Just $  FunType logicalType 
--                                        PFunArr sfty ps) t2
--                   let args = typeNub tm q2p (args1 ++ args2)
                combs2 <- mapM ( \ (sa, ca, _, ta) -> do
                    let sr = compSubst sf sa
                    return [(sr, joinC ca $ substC sa cf, subst sr rty, 
                                     ApplTerm tf ta ps)]) args
                return $ concat combs2) ops
            let res = concat combs 
            if null res then 
               addDiags [case mt of 
                       Nothing -> mkDiag Error
                                  "untypable application" origAppl
                       Just ty -> mkDiag Hint 
                            ("untypable application (with result type: "
                            ++ showPretty ty ")\n")
                            origAppl]
               else return ()
            return res

-- True means possibly find a smaller type
infer :: Maybe Type -> Term 
      -> State Env [(Subst, Constraints, Type, Term)]
infer mt trm = do
    tm <- gets typeMap
    let mUnify = mgu tm mt . Just
        uniDiags = addDiags . map (improveDiag trm)
    as <- gets assumps
    vs <- gets localVars
    case trm of 
        qv@(QualVar (VarDecl _ t _ _))  -> return $
            case mt of 
                 Nothing -> [(eps, noC, t, qv)]
                 Just ty -> [(eps, insertC (Subtyping t ty) noC, t, qv)]
        QualOp br (InstOpId i ts qs) sc ps -> do
            (ty, inst, cs) <- instantiate sc
            let Result ds ms = mgu tm (if null ts then inst else ts) inst
            uniDiags ds 
            return $ case ms of 
                Nothing -> []
                Just s -> let q@(_, ncs, nTy, qv) = 
                                  (s, substC s cs, subst s ty, 
                                   QualOp br (InstOpId i (map (subst s) inst)
                                              qs) sc ps) in case mt of 
                    Nothing -> [q]
                    Just inTy -> [(s, insertC (Subtyping nTy $ subst s inTy) 
                                   ncs, nTy, qv)]
        ResolvedMixTerm i ts ps ->
            if null ts then do 
               let ois = case Map.lookup i vs of 
                         Nothing -> opInfos $ Map.findWithDefault 
                                    (OpInfos []) i as
                         Just t -> [OpInfo (simpleTypeScheme t) [] VarDefn]
               insts <- mapM instOpInfo ois 
               ls <- case mt of 
                     Nothing -> return $ map ( \ (ty, is, cs, oi) 
                                              -> (eps, ty, is, cs, oi)) insts
                     Just inTy -> do 
                         let rs = map ( \ (ty, is, cs, oi) ->
                                  (eps, ty, is, 
                                   insertC (Subtyping ty inTy) cs, oi)) insts
                         if null rs then 
                            addDiags [Diag Hint
                               ("no type match for: " ++ showId i "\n"
                                ++ lookupError inTy ois)
                               (posOfId i) ]
                            else return ()
                         return rs
               return $ {- typeNub tm q2p $ -} map ( \ (s, ty, is, cs, oi) -> 
                              case opDefn oi of
                              VarDefn -> (s, cs, ty, QualVar $ 
                                          VarDecl i ty Other ps)
                              x -> let br = case x of
                                            NoOpDefn v -> v
                                            Definition v _ -> v
                                            _ -> Op in 
                                      (s, cs, ty, 
                                       QualOp br (InstOpId i is [])
                                                  (opType oi) ps)) ls
            else inferAppl ps mt (ResolvedMixTerm i [] ps)
                 $ mkTupleTerm ts ps
        ApplTerm t1 t2 ps -> inferAppl ps mt t1 t2
        TupleTerm ts ps -> 
            case mt of 
            Nothing -> do                   
                ls <- checkList (map (const Nothing) ts) ts 
                return $ map ( \ (su, cs, tys, trms) ->
                                   (su, cs, mkProductType tys ps, 
                                    mkTupleTerm trms ps)) ls
            Just ty -> do 
                ls <- checkList (map (const Nothing) ts) ts 
                return $ map ( \ (su, cs, tys, trms) ->
                               let nTy = mkProductType tys ps in
                                   (su, insertC (Subtyping nTy
                                                $ subst su ty) cs, nTy,
                                    mkTupleTerm trms ps)) ls
        TypedTerm t qual ty ps -> do 
            case qual of 
                OfType -> do
                    let Result ds ms = mUnify ty
                    uniDiags ds
                    case ms of 
                        Nothing -> if lesserType tm ty $ fromJust mt then do 
                            rs <- infer (Just ty) t
                            return $ map ( \ (s2, cs, typ, tr) -> 
                                (s2, cs, typ, TypedTerm tr qual ty ps)) rs
                           else return []
                        Just s -> do 
                            rs <- infer (Just $ subst s ty) t 
                            return $ map ( \ (s2, cs, typ, tr) -> 
                                (compSubst s s2, substC s cs, typ, 
                                 TypedTerm tr qual ty ps)) rs
                InType -> do 
                    let Result ds ms = mUnify logicalType
                    uniDiags ds
                    case ms of 
                        Nothing -> return []
                        Just s -> do 
                            rs <- infer Nothing t
                            return $ map ( \ (s2, cs, typ, tr) -> 
                                (compSubst s s2, 
                                 substC s $ insertC (Subtyping ty typ) cs, 
                                 logicalType, 
                                 TypedTerm tr qual ty ps)) rs
                AsType -> do
                    let Result ds ms = mUnify ty
                    uniDiags ds
                    case ms of 
                        Nothing -> return []
                        Just s -> do 
                            rs <- infer Nothing t
                            return $ map ( \ (s2, cs, typ, tr) ->
                                (compSubst s s2, 
                                 substC s $ insertC (Subtyping ty typ) cs,
                                 ty, TypedTerm tr qual ty ps)) rs
        QuantifiedTerm quant decls t ps -> do
            mapM_ addGenLocalVar decls
            let Result ds ms = mUnify logicalType
            uniDiags ds
            case ms of 
                Nothing -> return []
                Just _ -> do 
                    rs <- infer (Just logicalType) t 
                    putLocalVars vs
                    putTypeMap tm
                    return $ map ( \ (s, cs, typ, tr) -> 
                        (s, cs, typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do 
            pvs <- freshVars pats
            rty <- freshTypeVar $ posOfTerm resTrm
            let fty l = if null l then rty else 
                        FunType (head l) (case part of
                                          Partial -> PFunArr
                                          Total -> FunArr) (fty $ tail l) []
                myty = fty pvs
                Result ds ms = mUnify myty
            uniDiags ds 
            case ms of 
                Nothing -> return []
                Just s -> do 
                    ls <- checkList (map (Just . subst s) pvs) pats
                    rs <- mapM ( \ ( s2, cs, _, nps) -> do
                       mapM_ addLocalVar $ concatMap extractVars nps
                       let newS = compSubst s s2 
                       es <- infer (Just $ subst newS rty) resTrm
                       putLocalVars vs
                       return $ map ( \ (s3, cr, _, rtm) -> 
                                      (compSubst newS s3, 
                                       substC s3 cs `joinC` cr,
                                       subst s3 (subst newS myty), 
                                       LambdaTerm nps part rtm ps)) es) ls
                    return $ concat rs 
        CaseTerm ofTrm eqs ps -> do 
            ts <- infer Nothing ofTrm
            rty <- case mt of 
                   Nothing -> freshTypeVar $ posOfTerm trm
                   Just ty -> return ty
            if null ts then addDiags [mkDiag Error 
                                      "unresolved of-term in case" ofTrm]
                else return () 
            rs <- mapM ( \ (s1, cs, oty, otrm) -> do 
                 es <- inferCaseEqs oty (subst s1 rty) eqs
                 return $ map ( \ (s2, cr, _, ty, nes) ->
                                (compSubst s1 s2, 
                                 substC s2 cs `joinC` cr, ty, 
                                 CaseTerm otrm nes ps)) es) ts
            return $ concat rs
        LetTerm br eqs inTrm ps -> do 
            es <- inferLetEqs eqs
            rs <- mapM ( \ (s1, cs, _, nes) -> do 
               mapM_ addLocalVar $ concatMap (\ (ProgEq p _ _) -> 
                                             extractVars p) nes
               ts <- infer mt inTrm 
               return $ map ( \ (s2, cr, ty, nt) -> 
                              (compSubst s1 s2, 
                               substC s2 cs `joinC` cr,
                               ty, 
                               LetTerm br nes nt ps)) ts) es
            putLocalVars vs
            return $ concat rs
        AsPattern (VarDecl v _ ok qs) pat ps -> do 
           pats <- infer mt pat
           return $ map ( \ (s1, cs, t1, p1) -> (s1, cs, t1, 
                          AsPattern (VarDecl v t1 ok qs) p1 ps)) pats
        _ -> do ty <- freshTypeVar $ posOfTerm trm
                addDiags [mkDiag Error "unexpected term" trm]
                return [(eps, noC, ty, trm)]

inferLetEqs :: [ProgEq] -> State Env [(Subst, Constraints, [Type], [ProgEq])]
inferLetEqs es = do
    let pats = map (\ (ProgEq p _ _) -> p) es 
        trms = map (\ (ProgEq _ t _) -> t) es
        qs = map (\ (ProgEq _ _ q) -> q) es
    do vs <- gets localVars
       newPats <- checkList (map (const Nothing) pats) pats
       combs <- mapM ( \ (sf, pcs, tys, pps) -> do
             mapM_ addLocalVar $ concatMap extractVars pps 
             newTrms <- checkList (map Just tys) trms 
             return $ map ( \ (sr, tcs, tys2, tts ) ->  
                          (compSubst sf sr, 
                           joinC tcs $ substC sr pcs, tys2, 
                           zipWith3 ( \ p t q -> ProgEq (substTerm sr p) t q)
                               pps tts qs)) newTrms) newPats
       putLocalVars vs                                       
       return $ concat combs 

inferCaseEq :: Type -> Type -> ProgEq 
            -> State Env [(Subst, Constraints, Type, Type, ProgEq)]
inferCaseEq pty tty (ProgEq pat trm ps) = do
   as <- gets assumps
   let newAs = filterAssumps ( \ o -> case opDefn o of
                                              ConstructData _ -> True
                                              VarDefn -> True
                                              _ -> False) as
   putAssumps newAs
   pats <- infer (Just pty) pat >>= reduce False
   putAssumps as
   if null pats then addDiags [mkDiag Error "unresolved case pattern" pat]
      else return ()
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do 
                mapM_ addLocalVar $ extractVars p
                ts <- infer (Just $  subst s tty) trm >>= reduce False
                putLocalVars vs
                return $ map ( \ (st, cr, tyt, t) -> 
                       (compSubst s st, 
                        substC st cs `joinC` cr,
                        subst st ty, tyt, 
                        ProgEq p t ps)) ts) pats
   return $ concat es

inferCaseEqs :: Type -> Type -> [ProgEq] 
            -> State Env [(Subst, Constraints, Type, Type, [ProgEq])]
inferCaseEqs pty tTy [] = return [(eps, noC, pty, tTy, [])]
inferCaseEqs pty tty (eq:eqs) = do 
  fts <- inferCaseEq pty tty eq
  rs <- mapM (\ (_, cs, pty1, tty1, ne) -> do 
              rts <- inferCaseEqs pty1 tty1 eqs
              return $ map ( \ (s2, cr, pty2, tty2, nes) ->
                             (s2, 
                              substC s2 cs `joinC` cr,
                              pty2, tty2, ne:nes)) rts) fts
  return $ concat rs

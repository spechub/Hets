
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
import HasCASL.Constrain
import HasCASL.ProgEq
import HasCASL.MinType

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.Lib.State

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
     return (typ, inst, Set.fromList $ foldr ( \ ty@(TypeName _ k _) l
                                     -> case k of 
                                        Intersection [] _ -> l
                                        _ -> Kinding ty k : l) [] inst)

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
                      vs <- gets localVars
                      putLocalVars $ Map.map (subst sf) vs
                      rts <- checkList (map (fmap (subst sf)) rty) rt
                      putLocalVars vs
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
                vs <- gets localVars
                putLocalVars $ Map.map (subst sf) vs
                args1 <- infer (Just sfty) t2 >>= reduce False
                putLocalVars $ Map.map (subst sf) vs            
                args2 <- infer (Just $ liftType sfty ps) t2 >>= reduce False
                putLocalVars vs
                let args = args1 ++ args2
                    combs2 = map ( \ (sa, ca, _, ta) ->
                        let sr = compSubst sf sa in
                          [(sr, joinC ca $ substC sa cf, subst sr rty, 
                                     ApplTerm tf ta ps)]) args
                return $ concat combs2) ops
            let res = concat combs 
            if null res then 
               addDiags [case mt of 
                       Nothing -> mkDiag Hint
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
            addDiags $ map (improveDiag trm) ds 
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
               let ls = map ( \ (ty, is, cs, oi) ->
                              (eps, ty, is, case mt of 
                               Just inTy -> insertC (Subtyping ty inTy) cs
                               Nothing -> cs, oi)) insts
               if null ls then addDiags 
                   [Diag Hint
                       ("no type match for: " ++ showId i "" ++ case mt of 
                        Nothing -> ""
                        Just inTy -> '\n' : lookupError inTy ois) (posOfId i)]
                   else return ()
               return $ typeNub tm q2p $ map ( \ (s, ty, is, cs, oi) -> 
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
        TupleTerm ts ps -> if null ts then return 
            [(eps, case mt of 
              Nothing -> noC
              Just ty -> insertC (Subtyping logicalType ty) noC,
              logicalType, trm)]
            else do
                ls <- checkList (map (const Nothing) ts) ts 
                return $ map ( \ (su, cs, tys, trms) ->
                    let nTy = mkProductType tys ps in
                               (su, case mt of 
                                Nothing -> cs
                                Just ty -> insertC (Subtyping nTy
                                                   $ subst su ty) cs, nTy,
                                mkTupleTerm trms ps)) ls
        TypedTerm t qual ty ps -> do 
            case qual of 
                InType -> do 
                    vTy <- freshTypeVar $ headPos ps
                    rs <- infer Nothing t
                    return $ map ( \ (s, cs, typ, tr) -> 
                           let sTy = subst s ty in
                               (s,  insertC (Subtyping sTy vTy) 
                               $ insertC (Subtyping typ vTy) 
                               $ case mt of
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping (subst s jTy)
                                                      logicalType) cs,
                                 logicalType, 
                                 TypedTerm tr qual sTy ps)) rs
                AsType -> do
                    vTy <- freshTypeVar $ headPos ps
                    rs <- infer Nothing t
                    return $ map ( \ (s, cs, typ, tr) -> 
                        let sTy = subst s ty in
                                (s, insertC (Subtyping sTy vTy) 
                                $ insertC (Subtyping typ vTy) 
                                $ case mt of
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping (subst s jTy)
                                                      sTy) cs,
                                 sTy, TypedTerm tr qual sTy ps)) rs
                _ -> do
                    rs <- infer (Just ty) t
                    return $ map ( \ (s, cs, _, tr) -> 
                          let sTy = subst s ty in
                                (s, case mt of 
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping sTy
                                                      $ subst s jTy) cs,
                                 sTy, TypedTerm tr qual sTy ps)) rs
        QuantifiedTerm quant decls t ps -> do
            mapM_ addGenLocalVar decls
            rs <- infer (Just logicalType) t 
            putLocalVars vs
            putTypeMap tm
            return $ map ( \ (s, cs, typ, tr) -> 
                        (s, case mt of 
                         Nothing -> cs
                         Just ty -> insertC (Subtyping (subst s ty) 
                                             logicalType) cs, 
                         typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do 
            pvs <- freshVars pats
            rty <- freshTypeVar $ posOfTerm resTrm
            let fty l = if null l then rty else 
                        FunType (head l) (if null (tail l) then case part of
                                          Partial -> PFunArr
                                          Total -> FunArr
                                         else FunArr) (fty $ tail l) []
                myty = fty pvs
            ls <- checkList (map Just pvs) pats
            rs <- mapM ( \ ( s, cs, _, nps) -> do
                       mapM_ addLocalVar $ concatMap extractVars nps
                       es <- infer (Just $ subst s rty) resTrm
                       putLocalVars vs
                       return $ map ( \ (s2, cr, _, rtm) -> 
                                      let s3 = compSubst s s2
                                          typ = subst s3 myty in
                                      (s3, joinC (substC s2 cs) $ 
                                       case mt of 
                                       Nothing -> cr
                                       Just ty -> insertC (Subtyping typ 
                                                          $ subst s2 ty) cr,
                                       typ, 
                                       LambdaTerm nps part rtm ps)) es) ls
            return $ concat rs 
        CaseTerm ofTrm eqs ps -> do 
            ts <- infer Nothing ofTrm
            rty <- case mt of 
                   Nothing -> freshTypeVar $ posOfTerm trm
                   Just ty -> return ty
            if null ts then addDiags [mkDiag Hint 
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
   pats1 <- infer (Just pty) pat >>= reduce False
   e <- get            
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
   if null pats then addDiags [mkDiag Hint "unresolved case pattern" pat]
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

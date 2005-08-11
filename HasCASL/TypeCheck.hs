{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

type inference based on

<http://www.cs.fiu.edu/~smithg/papers/>

Principal Type Schemes for Functional Programs with Overloading and
Subtyping, Geoffrey S. Smith, Science of Computer Programming 23(2-3),
pp. 197-226, December 1994

-}

module HasCASL.TypeCheck where

import HasCASL.Unify 
import HasCASL.AsUtils
import HasCASL.Merge
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.Le
import HasCASL.MixAna
import HasCASL.TypeAna
import HasCASL.MapTerm
import HasCASL.Constrain
import HasCASL.ProgEq
import HasCASL.MinType

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.PrettyPrint
import Common.GlobalAnnotations
import Common.Lib.State

import Data.List as List

import Control.Exception(assert)

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
              Just np -> typeCheck Nothing np

instantiate :: TypeScheme -> State Env (Type, [Type], Constraints)
instantiate (TypeScheme tArgs t _) = 
    do let ls = leaves (< 0) t -- generic vars
           vs = map snd ls
       ts <- toEnvState $ mkSubst vs
       let s = Map.fromList $ zip (map fst ls) ts
           (ats, cs) = unzip $ mapArgs s (zip (map fst vs) ts) tArgs
       return (subst s t, ats, Set.fromList cs)

mapArgs :: Subst -> [(Id, Type)] -> [TypeArg] -> [(Type, Constrain)]
mapArgs s ts = foldr ( \ (TypeArg i _ vk _ _ _ _) l ->  
    maybe l ( \ (_, t) -> (t, case vk of
        MissingKind -> error "mapArgs"
        VarKind k -> Kinding t k
        Downset super -> Subtyping t $ subst s super) : l) $ 
            find ( \ (j, _) -> i == j) ts) []

instOpInfo :: OpInfo -> State Env (Type, [Type], Constraints, OpInfo)
instOpInfo oi = do
     (ty, inst, cs) <- instantiate $ opType oi
     return (ty, inst, cs, oi)

lookupError :: Type -> [OpInfo] -> String
lookupError ty ois = 
    "  with (maximal) type: " ++  showPretty ty "\n"
    ++ "  known types:\n    " ++
       showSepList ("\n    "++) (showPretty . opType) ois "" 

checkList :: Bool -> [Maybe Type] -> [Term] 
          -> State Env [(Subst, Constraints, [Type], [Term])]
checkList _ [] [] = return [(eps, noC, [], [])]
checkList b (ty : rty) (trm : rt) = do 
      fts <- infer b ty trm >>= reduce False 
      combs <- mapM ( \ (sf, cs, tyf, tf) -> do
                      vs <- gets localVars
                      putLocalVars $ substVarTypes sf vs
                      rts <- checkList b (map (fmap (subst sf)) rty) rt
                      putLocalVars vs
                      return $ map ( \ (sr, cr, tys, tts) ->
                             (compSubst sf sr, 
                              substC sr cs `joinC` cr,
                              subst sr tyf : tys,
                                     tf : tts)) rts) fts
      return $ concat combs
checkList _ _ _ = error "checkList"

-- | reduce a substitution, if true try to find a monomorphic substitution
reduce :: Bool -> [(Subst, Constraints, Type, Term)] 
       -> State Env [(Subst, Constraints, Type, Term)]
reduce b alts = do
       te <- get
       combs <- mapM ( \ (s, cr, ty, tr) -> do 
           Result ds mc <- toEnvState $ shapeRel te cr
           addDiags $ map (improveDiag tr) ds 
           return $ case mc of 
               Nothing -> []
               Just (cs, qs, trel) -> let 
                   s1 = compSubst s cs
                   ms = if b then monoSubsts te 
                       (Rel.transClosure $ Rel.union (fromTypeMap $ typeMap te)
                          $ trel) (subst cs ty)
                       else eps
                   s2 = compSubst s1 ms 
                   in [(s2, substC ms $ foldr ( \ (a, t) -> insertC 
                                     (Subtyping a t)) 
                        qs $ Rel.toList trel, subst s2 ty, 
                                     substTerm s2 tr)]) alts
       return $ concat combs

typeCheck :: Maybe Type -> Term -> State Env (Maybe Term)
typeCheck mt trm = do
    e <- get
    mtrm <- typeCheck0 False mt trm
    case mtrm of 
        Nothing -> do 
            put e
            addDiags [mkDiag Warning "trying hard to find lazy type for" trm]
            typeCheck0 True mt trm
        Just _ -> return mtrm

typeCheck0 :: Bool -> Maybe Type -> Term -> State Env (Maybe Term)
typeCheck0 b mt trm = 
    do alts <- infer b mt trm >>= reduce True 
       te <- get
       let p = getRange trm
       if null alts then 
          do addDiags [mkDiag Error "no typing for" trm]
             return Nothing
          else if null $ tail alts then do
               let (_, cs, ty, t) = head alts
                   (ds, rcs) = simplify te cs 
                   es = map ( \ d -> d {diagKind = Hint, diagPos = p}) ds
               addDiags es 
               if Set.null rcs then return ()
                  else addDiags [(mkDiag Error ("in term'"
                             ++ showPretty t "' of type '" 
                             ++ showPretty ty "'\n unresolved constraints")
                                 rcs){diagPos = p}]
               return $ Just t
          else let alts3 = filter ( \ (_, cs, _, _) -> 
                             Set.null $ snd $ simplify te cs) alts 
                   falts = typeNub te q2p alts3 in
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

freshTypeVar :: Range -> State Env Type             
freshTypeVar p = 
    do (var, c) <- toEnvState $ freshVar p
       return $ TypeName var rStar c

freshVars :: [Term] -> State Env [Type]
freshVars l = mapM (freshTypeVar . posOfTerm) l

substVarTypes :: Subst -> Map.Map Id VarDefn -> Map.Map Id VarDefn
substVarTypes s = Map.map ( \ (VarDefn t) -> VarDefn $ subst s t)

-- | infer type of application, if true consider lifting for lazy types
inferAppl :: Bool -> Range -> Maybe Type -> Term  -> Term 
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl b ps mt t1 t2 = do
            let origAppl = ApplTerm t1 t2 ps
            aty <- freshTypeVar $ posOfTerm t2
            rty <- case mt of 
                Nothing -> freshTypeVar $ posOfTerm t1
                Just ty -> return ty
            ops <- infer b (Just $ FunType aty PFunArr rty nullRange) t1 
                   >>= reduce False
            combs <- mapM ( \ (sf, cf, funty, tf) -> do 
                let (sfty, frty) = case funty of 
                          FunType paty _ prty _ -> (paty, prty)
                          _ -> (subst sf aty, subst sf rty)
                vs <- gets localVars
                putLocalVars $ substVarTypes sf vs
                args1 <- infer b (Just sfty) t2 >>= reduce False
                args2 <- if b then do 
                            putLocalVars $ substVarTypes sf vs            
                            infer b (Just $ liftType sfty ps) t2 
                                      >>= reduce False
                         else return []
                putLocalVars vs
                let args = args1 ++ args2
                    combs2 = map ( \ (sa, ca, _, ta) ->
                        let sr = compSubst sf sa 
                            nTy = subst sa frty in 
                          [(sr, joinC ca $ substC sa cf, nTy, 
                            TypedTerm (ApplTerm tf ta ps) 
                            Inferred nTy ps)]) args
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


getTypeOf :: Term -> Type
getTypeOf trm = case trm of
    TypedTerm _ q t _ -> case q of InType -> unitType
                                   _ -> t
    QualVar (VarDecl _ t _ _) -> t
    QualOp _ _ (TypeScheme [] t _) _ -> t
    TupleTerm ts ps -> if null ts then unitType
                       else mkProductType (map getTypeOf ts) ps
    QuantifiedTerm _ _ t _ -> getTypeOf t
    LetTerm _ _ t _ -> getTypeOf t
    AsPattern _ p _ -> getTypeOf p
    _ -> error "getTypeOf"

-- | infer type of term, if true consider lifting for lazy types
infer :: Bool -> Maybe Type -> Term 
      -> State Env [(Subst, Constraints, Type, Term)]
infer b mt trm = do
    e <- get
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
            let Result ds ms = mguList tm (if null ts then inst else ts) inst
            addDiags $ map (improveDiag trm) ds 
            return $ case ms of 
                Nothing -> []
                Just s -> 
                    let nTy = subst s ty
                        ncs = substC s cs
                        qv = TypedTerm (QualOp br 
                             (InstOpId i (map (subst s) inst) qs) sc ps)
                             Inferred nTy ps
                    in case mt of                         
                    Nothing -> [(s, ncs, nTy, qv)]
                    Just inTy -> [(s, insertC (Subtyping nTy $ subst s inTy) 
                                   ncs, nTy, qv)]
        ResolvedMixTerm i ts ps ->
            if null ts then case Map.lookup i vs of 
               Just (VarDefn t) -> infer b mt $ QualVar $ VarDecl i t Other ps
               Nothing -> do
                    let ois = opInfos $ Map.findWithDefault (OpInfos []) i as
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
                    return $ typeNub e q2p $ map 
                      ( \ (s, ty, is, cs, oi) -> 
                        let od = opDefn oi
                            br = case od of
                                 NoOpDefn v -> v
                                 Definition v _ -> v
                                 _ -> Op 
                       in (s, cs, ty, case opType oi of 
                           sc@(TypeScheme [] sTy _) -> assert (sTy == ty) $
                                  QualOp br (InstOpId i [] nullRange) sc ps
                           sc -> TypedTerm (QualOp br 
                                       (InstOpId i is nullRange) sc ps)
                                       Inferred ty ps)) ls
            else inferAppl b ps mt (ResolvedMixTerm i [] ps)
                 $ mkTupleTerm ts ps
        ApplTerm t1 t2 ps -> inferAppl b ps mt t1 t2
        TupleTerm ts ps -> if null ts then return 
            [(eps, case mt of 
              Nothing -> noC
              Just ty -> insertC (Subtyping unitType ty) noC,
              unitType, trm)]
            else do
                ls <- checkList b (map (const Nothing) ts) ts 
                return $ map ( \ (su, cs, tys, trms) ->
                    let nTy = mkProductType tys ps in
                               (su, case mt of 
                                Nothing -> cs
                                Just ty -> insertC (Subtyping nTy
                                                   $ subst su ty) cs, nTy,
                                assert (and $ zipWith (==) tys 
                                       $ map (subst su . getTypeOf) trms) $
                                mkTupleTerm trms ps)) ls
        TypedTerm t qual ty ps -> do 
            case qual of 
                InType -> do 
                    vTy <- freshTypeVar ps
                    rs <- infer b Nothing t
                    return $ map ( \ (s, cs, typ, tr) -> 
                           let sTy = subst s ty in
                               (s,  insertC (Subtyping sTy vTy) 
                               $ insertC (Subtyping typ vTy) 
                               $ case mt of
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping (subst s jTy)
                                                      unitType) cs,
                                 unitType, 
                                 TypedTerm tr qual sTy ps)) rs
                AsType -> do
                    vTy <- freshTypeVar ps
                    rs <- infer b Nothing t
                    return $ map ( \ (s, cs, typ, tr) -> 
                        let sTy = subst s ty in
                                (s, insertC (Subtyping sTy vTy) 
                                $ insertC (Subtyping typ vTy) 
                                $ case mt of
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping sTy 
                                                      $ subst s jTy) cs,
                                 sTy, TypedTerm tr qual sTy ps)) rs
                _ -> do
                    rs <- infer b (Just ty) t
                    return $ map ( \ (s, cs, _, tr) -> 
                          let sTy = subst s ty in
                                (s, case mt of 
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping sTy
                                                      $ subst s jTy) cs,
                                 sTy, if getTypeOf tr == sTy then tr
                                      else TypedTerm tr qual sTy ps)) rs
        QuantifiedTerm quant decls t ps -> do
            mapM_ addGenVarDecl decls
            rs <- infer b (Just unitType) t 
            putLocalVars vs
            putTypeMap tm
            return $ map ( \ (s, cs, typ, tr) -> 
                        (s, case mt of 
                         Nothing -> cs
                         Just ty -> insertC (Subtyping (subst s ty) 
                                             unitType) cs, 
                         typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do 
            pvs <- freshVars pats
            rty <- freshTypeVar $ posOfTerm resTrm
            let myty = getFunType rty part pvs
            ls <- checkList b (map Just pvs) pats
            rs <- mapM ( \ ( s, cs, _, nps) -> do
                       mapM_ (addLocalVar True) $ concatMap extractVars nps
                       es <- infer b (Just $ subst s rty) resTrm
                       putLocalVars vs
                       return $ map ( \ (s2, cr, _, rtm) -> 
                                      let s3 = compSubst s s2
                                          typ = subst s3 myty in
                                      (s3, joinC (substC s2 cs) $ 
                                       case mt of 
                                       Nothing -> cr
                                       Just ty -> insertC (Subtyping typ 
                                                          $ subst s3 ty) cr,
                                       typ, TypedTerm
                                       (LambdaTerm nps part rtm ps)
                                       Inferred typ ps)) es) ls
            return $ concat rs 
        CaseTerm ofTrm eqs ps -> do 
            ts <- infer b Nothing ofTrm
            rty <- case mt of 
                   Nothing -> freshTypeVar $ posOfTerm trm
                   Just ty -> return ty
            if null ts then addDiags [mkDiag Hint 
                                      "unresolved of-term in case" ofTrm]
                else return () 
            rs <- mapM ( \ (s1, cs, oty, otrm) -> do 
                 es <- inferCaseEqs b oty (subst s1 rty) eqs
                 return $ map ( \ (s2, cr, _, ty, nes) ->
                                (compSubst s1 s2, 
                                 substC s2 cs `joinC` cr, ty, 
                                 TypedTerm (CaseTerm otrm nes ps)
                                 Inferred ty ps)) es) ts
            return $ concat rs
        LetTerm br eqs inTrm ps -> do 
            es <- inferLetEqs b eqs
            rs <- mapM ( \ (s1, cs, _, nes) -> do 
               mapM_ (addLocalVar True) $ concatMap 
                         ( \ (ProgEq p _ _) -> extractVars p) nes
               ts <- infer b mt inTrm 
               return $ map ( \ (s2, cr, ty, nt) -> 
                              (compSubst s1 s2, 
                               substC s2 cs `joinC` cr,
                               ty, assert (getTypeOf nt == ty) $ 
                               LetTerm br nes nt ps)) ts) es
            putLocalVars vs
            return $ concat rs
        AsPattern (VarDecl v _ ok qs) pat ps -> do 
           pats <- infer b mt pat
           return $ map ( \ (s1, cs, t1, p1) -> (s1, cs, t1, 
                          AsPattern (VarDecl v t1 ok qs) p1 ps)) pats
        _ -> do ty <- freshTypeVar $ posOfTerm trm
                addDiags [mkDiag Error "unexpected term" trm]
                return [(eps, noC, ty, trm)]

inferLetEqs :: Bool -> [ProgEq] 
            -> State Env [(Subst, Constraints, [Type], [ProgEq])]
inferLetEqs b es = do
    let pats = map (\ (ProgEq p _ _) -> p) es 
        trms = map (\ (ProgEq _ t _) -> t) es
        qs = map (\ (ProgEq _ _ q) -> q) es
    do vs <- gets localVars
       newPats <- checkList b (map (const Nothing) pats) pats
       combs <- mapM ( \ (sf, pcs, tys, pps) -> do
             mapM_ (addLocalVar True) $ concatMap extractVars pps
             newTrms <- checkList b (map Just tys) trms 
             return $ map ( \ (sr, tcs, tys2, tts ) ->  
                          (compSubst sf sr, 
                           joinC tcs $ substC sr pcs, tys2, 
                           zipWith3 ( \ p t q -> ProgEq (substTerm sr p) t q)
                               pps tts qs)) newTrms) newPats
       putLocalVars vs                                       
       return $ concat combs 

inferCaseEq :: Bool -> Type -> Type -> ProgEq 
            -> State Env [(Subst, Constraints, Type, Type, ProgEq)]
inferCaseEq b pty tty (ProgEq pat trm ps) = do
   pats1 <- infer b (Just pty) pat >>= reduce False
   e <- get            
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
   if null pats then addDiags [mkDiag Hint "unresolved case pattern" pat]
      else return ()
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do 
                mapM_ (addLocalVar True) $ extractVars p
                ts <- infer b (Just $  subst s tty) trm >>= reduce False
                putLocalVars vs
                return $ map ( \ (st, cr, tyt, t) -> 
                       (compSubst s st, 
                        substC st cs `joinC` cr,
                        subst st ty, tyt, 
                        ProgEq p t ps)) ts) pats
   return $ concat es

inferCaseEqs :: Bool -> Type -> Type -> [ProgEq] 
            -> State Env [(Subst, Constraints, Type, Type, [ProgEq])]
inferCaseEqs _ pty tTy [] = return [(eps, noC, pty, tTy, [])]
inferCaseEqs b pty tty (eq:eqs) = do 
  fts <- inferCaseEq b pty tty eq
  rs <- mapM (\ (_, cs, pty1, tty1, ne) -> do 
              rts <- inferCaseEqs b pty1 tty1 eqs
              return $ map ( \ (s2, cr, pty2, tty2, nes) ->
                             (s2, 
                              substC s2 cs `joinC` cr,
                              pty2, tty2, ne:nes)) rts) fts
  return $ concat rs

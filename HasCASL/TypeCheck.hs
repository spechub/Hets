{- |
Module      :  $Header$
Description :  type checking terms and program equations
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

type inference based on

<http://www.cs.fiu.edu/~smithg/papers/>

Principal Type Schemes for Functional Programs with Overloading and
Subtyping, Geoffrey S. Smith, Science of Computer Programming 23(2-3),
pp. 197-226, December 1994
-}

module HasCASL.TypeCheck
    ( typeCheck
    , resolveTerm
    ) where

import HasCASL.Unify
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.FoldType
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.AsUtils
import HasCASL.MixAna
import HasCASL.TypeAna
import HasCASL.MapTerm
import HasCASL.FoldTerm
import HasCASL.Constrain
import HasCASL.ProgEq
import HasCASL.MinType

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.DocUtils
import Common.Lib.State

import Data.List as List
import Data.Maybe (catMaybes)

substTerm :: Subst -> Term -> Term
substTerm s = mapTerm (id, subst s)

-- | mixfix and type resolution
resolveTerm :: Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm mt trm = do
    mtrm <- resolve trm
    case mtrm of
      Nothing -> return Nothing
      Just t -> typeCheck mt t

-- | get a constraint from a type argument instantiated with a type
mkConstraint :: (Type, VarKind) -> Constrain
mkConstraint (ty, vk) = case vk of
    MissingKind -> error "mkConstraint"
    VarKind k -> Kinding ty k
    Downset super -> Subtyping ty super

instantiate :: [Type] -> TypeScheme
            -> State Env (Maybe (Type, [(Type, VarKind)]))
instantiate tys sc@(TypeScheme tArgs t _) =
    if null tys || length tys /= length tArgs then
         if null tys then fmap Just $ toEnvState $ freshInst sc
         else do
             addDiags [mkDiag Hint ("for type scheme '" ++
                 showDoc t "' wrong length of instantiation list") tys]
             return Nothing
        else let s = Map.fromList $ zip [-1, -2..] tys
             in return $ Just
                (substGen s t, zip tys $ map (substTypeArg s) tArgs)

instOpInfo :: [Type] -> OpInfo
           -> State Env (Maybe (Type, [Type], Constraints, OpInfo))
instOpInfo tys oi = do
     m <- instantiate tys $ opType oi
     return $ case m of
       Just (ty, cl) ->
           Just (ty, map fst cl, Set.fromList $ map mkConstraint cl, oi)
       Nothing -> Nothing

checkList :: Bool -> [Maybe Type] -> [Term]
          -> State Env [(Subst, Constraints, [Type], [Term])]
checkList isP mtys trms = case (mtys, trms) of
    (ty : rty, trm : rt) -> do
      fts <- infer isP ty trm >>= reduce
      combs <- mapM ( \ (sf, cs, tyf, tf) -> do
                      vs <- gets localVars
                      putLocalVars $ substVarTypes sf vs
                      rts <- checkList isP (map (fmap (subst sf)) rty) rt
                      putLocalVars vs
                      return $ map ( \ (sr, cr, tys, tts) ->
                             (compSubst sf sr,
                              substC sr cs `joinC` cr,
                              subst sr tyf : tys,
                                     tf : tts)) rts) fts
      return $ concat combs
    _ -> return [(eps, noC, [], [])]

-- | reduce a substitution
reduce :: [(Subst, Constraints, Type, Term)]
       -> State Env [(Subst, Constraints, Type, Term)]
reduce alts = do
       te <- get
       combs <- mapM ( \ (s, cr, ty, tr) -> do
           Result ds mc <- toEnvState $ shapeRel te $ joinC cr
                           $ fromTypeVars $ localTypeVars te
           addDiags $ map (improveDiag tr) ds
           return $ case mc of
               Nothing -> []
               Just (cs, qs, trel) -> let
                   s1 = compSubst s cs
                   ms = monoSubsts
                       (Rel.transClosure $ Rel.union (fromTypeMap $ typeMap te)
                          $ trel) (subst cs ty)
                   s2 = compSubst s1 ms
                   in [(s2, substC ms $ foldr ( \ (a, t) -> insertC
                                     (Subtyping a t))
                        qs $ Rel.toList trel, subst s2 ty,
                                     substTerm s2 tr)]) alts
       return $ concat combs

-- | type checking a term
typeCheck :: Maybe Type -> Term -> State Env (Maybe Term)
typeCheck mt trm =
    do alts <- infer False mt trm >>= reduce
       te <- get
       let p = getRange trm
           ga = globAnnos te
       if null alts then
          do addDiags [mkNiceDiag ga Error "no typing for" trm]
             return Nothing
          else if null $ tail alts then do
               let (_, cs, ty, t) = head alts
                   (ds, rcs) = simplify te cs
                   es = map ( \ d -> d {diagKind = Hint, diagPos = p}) ds
                   tys = getAllVarTypes t
               addDiags es
               if Set.null rcs then return ()
                  else addDiags [(mkDiag Error ("in term '"
                             ++ showGlobalDoc ga t "' of type '"
                             ++ showDoc ty "'\n unresolved constraints")
                                 rcs){diagPos = p}]
               if null tys then return ()
                  else addDiags [(mkDiag Error ("in term '"
                             ++ showGlobalDoc ga t
                             "'\n are uninstantiated type variables")
                                 $ Set.toList $ Set.unions $ map
                                    (Set.fromList . map (fst . snd) .
                                        leaves (> 0)) tys)
                                 {diagPos = p}]
               return $ Just t
          else let alts3 = filter ( \ (_, cs, _, _) ->
                             Set.null $ snd $ simplify te cs) alts
                   falts = typeNub te q2p alts3 in
               if null falts then do
                  addDiags [mkNiceDiag ga Error
                            "no constraint resolution for" trm]
                  addDiags $ map (\ (_, cs, _, _) -> (mkDiag Hint
                            "simplification failed for" cs){diagPos = p}) alts
                  return Nothing
               else if null $ tail falts then
                    let (_, _, _, t) = head falts in
                    return $ Just t
                    else
                    do addDiags [Diag Error
                         ("ambiguous typings\n " ++
                          showSepList ("\n " ++)
                          ( \ (n, t) -> shows n . (". " ++) . showDoc t)
                          (zip [1..(5::Int)] $ map ( \ (_,_,_,t) ->
                                          t) falts) "")
                            p]
                       return Nothing

freshTypeVar :: Term -> State Env Type
freshTypeVar t =
    do (var, c) <- toEnvState $ freshVar $ Id [] [] $ getRange t
       return $ TypeName var rStar c

substVarTypes :: Subst -> Map.Map Id VarDefn -> Map.Map Id VarDefn
substVarTypes s = Map.map ( \ (VarDefn t) -> VarDefn $ subst s t)

warnEmpty :: Maybe Type -> Term -> [a] -> State Env ()
warnEmpty mt trm res = do
    ga <- gets globAnnos
    if null res then addDiags [mkNiceDiag ga Hint ("untypeable term" ++
      case mt of
        Nothing -> ""
        Just ty -> " (with type: "  ++ showGlobalDoc ga ty ")") trm]
      else return ()

-- | infer type of application, consider lifting for lazy types
inferAppl :: Bool -> Range -> Maybe Type -> Term  -> Term
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl isP ps mt t1 t2 = do
    aty <- case t2 of
             TupleTerm [] _ -> return unitType
             _ -> freshTypeVar t2
    rty <- case mt of
             Nothing -> freshTypeVar t1
             Just ty -> return ty
    let mfrty = Just $ mkFunArrType aty PFunArr rty
        mlrty = Just $ TypeAppl lazyTypeConstr rty
    ops <- infer isP mfrty t1 >>= reduce
    lops <- case t2 of
        TupleTerm [] _ -> do
            laps <- infer isP mlrty t1 >>= reduce
            if null ops then warnEmpty mlrty t1 laps else return ()
            return laps
        _ -> do
          warnEmpty mfrty t1 ops
          return []
    let allOps = ops ++ lops
    if null allOps then return [] else do
        e <- get
        combs <- mapM ( \ (sf, cf, funty, tf) -> do
                let (sfty, frty) = case getTypeAppl funty of
                          (topTy, [paty, prty]) |
                            lesserType e topTy $ toFunType PFunArr ->
                                (paty, prty)
                          (topTy, [prty]) |
                            lesserType e topTy lazyTypeConstr ->
                                (unitType, prty)
                          _ -> (subst sf aty, subst sf rty)
                    msfty = Just sfty
                vs <- gets localVars
                putLocalVars $ substVarTypes sf vs
                args <- infer isP msfty t2 >>= reduce
                warnEmpty msfty t2 args
                putLocalVars vs
                let combs2 = map ( \ (sa, ca, _, ta) ->
                        let sr = compSubst sf sa
                            nTy = subst sa frty in
                          [(sr, joinC ca $ substC sa cf, nTy,
                            TypedTerm (ApplTerm tf
                            (mkTypedTerm ta $ subst sa sfty) ps)
                            Inferred nTy ps)]) args
                return $ concat combs2) allOps
        return $ concat combs

getAllVarTypes :: Term -> [Type]
getAllVarTypes = filter (not . null . leaves (> 0)) . getAllTypes

mkTypedTerm :: Term -> Type -> Term
mkTypedTerm trm ty = case trm of
    TupleTerm ts ps | not (null ts) -> let
      n = length ts
      (topTy, tArgs) = getTypeAppl ty
      in if n > 1 && topTy  == toProdType n nullRange
             && length tArgs == n then
      TupleTerm (zipWith mkTypedTerm ts tArgs) ps
      else TypedTerm trm Inferred ty ps
    _ -> TypedTerm trm Inferred ty nullRange

-- | infer type of term (or a pattern if the Bool is True)
infer :: Bool -> Maybe Type -> Term
      -> State Env [(Subst, Constraints, Type, Term)]
infer isP mt trm = do
    e <- get
    let tm = typeMap e
        as = assumps e
        bs = binders e
        vs = localVars e
        ga = globAnnos e
    case trm of
        qv@(QualVar (VarDecl _ ty _ ps))  -> return $
            case mt of
              Nothing -> [(eps, noC, ty, qv)]
              Just inTy -> [(eps, insertC (Subtyping ty inTy) noC,
                             inTy, TypedTerm qv Inferred inTy ps)]
        QualOp br i sc tys k ps -> do
            ms <- instOpInfo tys OpInfo { opType = sc
                                        , opAttrs = Set.empty
                                        , opDefn = NoOpDefn br }
            return $ case ms of
                Nothing -> []
                Just (ty, inst, cs, _) ->
                    let qv = TypedTerm (QualOp br i sc inst k ps)
                             Inferred ty ps
                    in case mt of
                    Nothing -> [(eps, cs, ty, qv)]
                    Just inTy -> [(eps, insertC (Subtyping ty inTy) cs,
                                   inTy, TypedTerm qv Inferred inTy ps)]
        ResolvedMixTerm i tys ts ps -> case (Map.lookup i bs, ts) of
          (Just j, hd : rt@(_ : _)) -> case reverse rt of
            lt : ft -> infer isP mt $ ResolvedMixTerm j tys
                (reverse $ LambdaTerm [hd] Partial lt ps : ft) ps
            [] -> error "ResolvedMixTerm: binder"
          _ ->
            if null ts then case Map.lookup i vs of
               Just (VarDefn t) ->
                 infer isP mt $ QualVar $ VarDecl i t Other ps
               Nothing -> do
                    insts <- mapM (instOpInfo tys) $ Set.toList
                             $ Map.findWithDefault Set.empty i as
                    let ls = map ( \ (ty, is, cs, oi) ->
                              (eps, ty, is, case mt of
                               Just inTy -> insertC (Subtyping ty inTy) cs
                               Nothing -> cs, oi)) $ catMaybes insts
                    if null ls then
                        addDiags [mkDiag Hint "no type found for" i]
                      else return ()
                    return $ map
                      ( \ (s, ty, is, cs, oi) ->
                        let od = opDefn oi
                            br = case od of
                                 NoOpDefn v -> v
                                 Definition v _ -> v
                                 _ -> Op
                            ik = if null tys then Infer else UserGiven
                       in (s, cs, ty, case opType oi of
                           sc@(TypeScheme [] _ _) ->
                                  QualOp br (PolyId i [] ps) sc [] ik ps
                           sc -> TypedTerm (QualOp br (PolyId i [] ps)
                                            sc is ik ps)
                                       Inferred ty ps)) ls
            else inferAppl isP ps mt (ResolvedMixTerm i tys [] ps)
                 $ mkTupleTerm ts ps
        ApplTerm t1 t2 ps -> inferAppl isP ps mt t1 t2
        TupleTerm ts ps -> if null ts then return
            [(eps, case mt of
              Nothing -> noC
              Just ty -> insertC (Subtyping unitType ty) noC,
              unitType, trm)]
            else do
                ls <- checkList isP (map (const Nothing) ts) ts
                return $ map ( \ (su, cs, tys, trms) ->
                    let nTy = mkProductTypeWithRange tys ps in
                               (su, case mt of
                                Nothing -> cs
                                Just ty -> insertC (Subtyping nTy
                                                   $ subst su ty) cs, nTy,
                                mkTupleTerm trms ps)) ls
        TypedTerm t qual ty ps -> do
            case qual of
                InType -> do
                    vTy <- freshTypeVar t
                    rs <- infer False Nothing t
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
                    vTy <- freshTypeVar t
                    rs <- infer False Nothing t
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
                    let decl = case t of
                          ResolvedMixTerm _ tys ts _
                              | isP && null tys && null ts && qual == OfType
                              -> True
                          _ -> False
                    rs <- infer isP (if decl then Nothing else Just ty) t
                    return $ map ( \ (s, cs, _, tr) ->
                          let sTy = subst s ty in
                                (s, case mt of
                                 Nothing -> cs
                                 Just jTy -> insertC (Subtyping sTy
                                                      $ subst s jTy) cs,
                                 sTy, case tr of
                                 QualVar (VarDecl vp _ po _)
                                     | decl -- shadow
                                     -> QualVar (VarDecl vp sTy po ps)
                                 _ -> if (qual == Inferred || case tr of
                                        QualVar _ -> True
                                        QualOp _ _ _ _ _ _ -> True
                                        TypedTerm _ OfType _ _ -> True
                                        _ -> False)
                                        && maybe False (eqStrippedType sTy)
                                               (getTypeOf tr)
                                      then tr
                                      else TypedTerm tr qual sTy ps)) rs
        QuantifiedTerm quant decls t ps -> do
            mapM_ addGenVarDecl decls
            rs <- infer False (Just unitType) t
            putLocalVars vs
            putTypeMap tm
            return $ map ( \ (s, cs, typ, tr) ->
                        (s, case mt of
                         Nothing -> cs
                         Just ty -> insertC (Subtyping (subst s ty)
                                             unitType) cs,
                         typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do
            pvs <- mapM freshTypeVar pats
            rty <- freshTypeVar resTrm
            let myty = getFunType rty part pvs
            ls <- checkList True (map Just pvs) pats
            rs <- mapM ( \ ( s, cs, _, nps) -> do
                       mapM_ (addLocalVar True) $ concatMap extractVars nps
                       es <- infer False (Just $ subst s rty) resTrm
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
            ts <- infer False Nothing ofTrm
            rty <- case mt of
                   Nothing -> freshTypeVar trm
                   Just ty -> return ty
            if null ts then addDiags [mkNiceDiag ga Hint
                                      "unresolved of-term in case" ofTrm]
                else return ()
            rs <- mapM ( \ (s1, cs, oty, otrm) -> do
                 es <- inferCaseEqs oty (subst s1 rty) eqs
                 return $ map ( \ (s2, cr, _, ty, nes) ->
                                (compSubst s1 s2,
                                 substC s2 cs `joinC` cr, ty,
                                 TypedTerm (CaseTerm otrm nes ps)
                                 Inferred ty ps)) es) ts
            return $ concat rs
        LetTerm br eqs inTrm ps -> do
            es <- inferLetEqs eqs
            rs <- mapM ( \ (s1, cs, _, nes) -> do
               mapM_ (addLocalVar True) $ concatMap
                         ( \ (ProgEq p _ _) -> extractVars p) nes
               ts <- infer False mt inTrm
               return $ map ( \ (s2, cr, ty, nt) ->
                              (compSubst s1 s2,
                               substC s2 cs `joinC` cr,
                               ty, LetTerm br nes nt ps)) ts) es
            putLocalVars vs
            return $ concat rs
        AsPattern (VarDecl v _ ok qs) pat ps -> do
           pats <- infer True mt pat
           return $ map ( \ (s1, cs, t1, p1) -> (s1, cs, t1,
                          AsPattern (VarDecl v t1 ok qs) p1 ps)) pats
        _ -> do ty <- freshTypeVar trm
                addDiags [mkNiceDiag ga Error "unexpected term" trm]
                return [(eps, noC, ty, trm)]

inferLetEqs :: [ProgEq] -> State Env [(Subst, Constraints, [Type], [ProgEq])]
inferLetEqs es = do
    let pats = map (\ (ProgEq p _ _) -> p) es
        trms = map (\ (ProgEq _ t _) -> t) es
        qs = map (\ (ProgEq _ _ q) -> q) es
    do vs <- gets localVars
       newPats <- checkList True (map (const Nothing) pats) pats
       combs <- mapM ( \ (sf, pcs, tys, pps) -> do
             mapM_ (addLocalVar True) $ concatMap extractVars pps
             newTrms <- checkList False (map Just tys) trms
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
   pats1 <- infer True (Just pty) pat >>= reduce
   e <- get
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
       ga = globAnnos e
   if null pats then addDiags [mkNiceDiag ga Hint
                               "unresolved case pattern" pat]
      else return ()
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do
                mapM_ (addLocalVar True) $ extractVars p
                ts <- infer False (Just $  subst s tty) trm >>= reduce
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
  rs <- mapM (\ (s, cs, pty1, tty1, ne) -> do
              rts <- inferCaseEqs pty1 tty1 eqs
              return $ map ( \ (s2, cr, pty2, tty2, nes) ->
                             (compSubst s s2,
                              substC s2 cs `joinC` cr,
                              pty2, tty2, ne:nes)) rts) fts
  return $ concat rs

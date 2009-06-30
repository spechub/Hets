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
import Common.GlobalAnnotations
import Common.Result
import Common.DocUtils
import Common.Utils
import Common.Lib.State

import Data.List as List
import Data.Maybe (catMaybes)
import Control.Monad (when, unless)

substTerm :: Subst -> Term -> Term
substTerm s = mapTerm (id, subst s)

-- | mixfix and type resolution
resolveTerm :: Type -> Term -> State Env (Maybe Term)
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
      fts <- inferWithMaybeType isP ty trm >>= reduce
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

checkForUninstantiatedVars :: GlobalAnnos -> Term -> Range -> State Env ()
checkForUninstantiatedVars ga t p = let
  tys = getAllVarTypes t
  in unless (null tys) $ addDiags
    [(mkDiag Error ("in term '" ++ showGlobalDoc ga t
                    "'\n are uninstantiated type variables")
      $ Set.toList $ Set.unions
      $ map (Set.fromList . map (fst . snd) . leaves (> 0)) tys)
     {diagPos = p}]

-- | type checking a term
typeCheck :: Type -> Term -> State Env (Maybe Term)
typeCheck exTy trm =
    do alts <- inferWithMaybeType False (Just exTy) trm >>= reduce
       te <- get
       let p = getRange trm
           ga = globAnnos te
       case alts of
         [] -> do
           addDiags [mkNiceDiag ga Error "no typing for" trm]
           return Nothing
         [(_, cs, ty, t)] -> do
           let (ds, rcs) = simplify te cs
               es = map ( \ d -> d {diagKind = Hint, diagPos = p}) ds
           addDiags es
           unless (Set.null rcs)
                 $ addDiags [(mkDiag Error ("in term '"
                             ++ showGlobalDoc ga t "' of type '"
                             ++ showDoc ty "'\n unresolved constraints")
                                 rcs){diagPos = p}]
           checkForUninstantiatedVars ga t p
           return $ Just t
         _ -> do
           let alts3 = filter ( \ (_, cs, _, _) ->
                             Set.null $ snd $ simplify te cs) alts
               falts = typeNub te q2p alts3
           case falts of
             [] -> do
               addDiags [mkNiceDiag ga Error "no constraint resolution for" trm]
               addDiags $ map (\ (_, cs, _, _) -> (mkDiag Hint
                            "simplification failed for" cs){diagPos = p}) alts
               return Nothing
             [(_, _, _, t)] -> do
               checkForUninstantiatedVars ga t p
               return $ Just t
             _ -> do
               addDiags [Diag Error
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
inferAppl :: Bool -> Range -> Term  -> Term
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl isP ps t1 t2 = do
    aty <- case t2 of
             TupleTerm [] _ -> return unitType
             _ -> freshTypeVar t2
    rty <- freshTypeVar t1
    let mfrty = Just $ mkFunArrType aty PFunArr rty
        mlrty = Just $ TypeAppl lazyTypeConstr rty
    ops <- inferWithMaybeType isP mfrty t1 >>= reduce
    lops <- case t2 of
        TupleTerm [] _ -> do
            laps <- inferWithMaybeType isP mlrty t1 >>= reduce
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
                args <- inferWithMaybeType isP msfty t2 >>= reduce
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
      in if n > 1 && topTy  == toProdType n ps
             && length tArgs == n then
      TupleTerm (zipWith mkTypedTerm ts tArgs) ps
      else TypedTerm trm Inferred ty ps
    LetTerm br eqs inTrm ps -> LetTerm br eqs (mkTypedTerm inTrm ty) ps
    QuantifiedTerm quant decls t ps ->
        QuantifiedTerm quant decls (mkTypedTerm t ty) ps
    _ -> TypedTerm trm Inferred ty $ getRange trm

lesserTypeScheme :: Env -> TypeScheme -> TypeScheme -> Bool
lesserTypeScheme e (TypeScheme args1 t1 _) (TypeScheme args2 t2 _) =
   if null args1 && null args2 then lesserType e t1 t2 else False

lesserOpInfo :: Env -> OpInfo -> OpInfo -> Bool
lesserOpInfo e o1 = lesserTypeScheme e (opType o1) . opType

addSuperType :: Type -> [(Subst, Constraints, Type, Term)]
             -> [(Subst, Constraints, Type, Term)]
addSuperType inTy =
  map (\ (s, c, ty, t) -> let nTy = subst s inTy in
       ( s, insertC (Subtyping ty nTy) c, nTy, mkTypedTerm t nTy))

-- | infer type of term (or a pattern if the Bool is True)
inferWithMaybeType :: Bool -> Maybe Type -> Term
                   -> State Env [(Subst, Constraints, Type, Term)]
inferWithMaybeType isP mt trm = do
  rs <- infer isP trm
  return $ case mt of
    Nothing -> rs
    Just ty -> addSuperType ty rs

-- | infer type of term (or a pattern if the Bool is True)
infer :: Bool -> Term -> State Env [(Subst, Constraints, Type, Term)]
infer isP trm = do
    e <- get
    let tm = typeMap e
        as = assumps e
        bs = binders e
        vs = localVars e
        ga = globAnnos e
    case trm of
        qv@(QualVar (VarDecl _ ty _ _))  -> return [(eps, noC, ty, qv)]
        QualOp br i sc tys k ps -> do
            ms <- instOpInfo tys OpInfo { opType = sc
                                        , opAttrs = Set.empty
                                        , opDefn = NoOpDefn br }
            return $ case ms of
                Nothing -> []
                Just (ty, inst, cs, _) ->
                    let qv = TypedTerm (QualOp br i sc inst k ps)
                             Inferred ty ps
                    in [(eps, cs, ty, qv)]
        ResolvedMixTerm i tys ts ps -> case (Map.lookup i bs, ts) of
          (Just j, hd : rt@(_ : _)) -> case reverse rt of
            lt : ft -> do
              pat <- anaPattern (Map.keysSet as) hd
              infer isP $ ResolvedMixTerm j tys
                (reverse $ LambdaTerm [pat] Partial lt ps : ft) ps
            [] -> error "ResolvedMixTerm: binder"
          _ ->
            if null ts then case Map.lookup i vs of
               Just (VarDefn t) ->
                 infer isP $ QualVar $ VarDecl i t Other ps
               Nothing -> do
                    insts <- mapM (instOpInfo tys)
                       $ keepMins (lesserOpInfo e)
                       $ Set.toList
                       $ Map.findWithDefault Set.empty i as
                    let ls = map ( \ (ty, is, cs, oi) ->
                              (eps, ty, is, cs, oi)) $ catMaybes insts
                    when (null ls) $
                        addDiags [mkDiag Hint "no type found for" i]
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
            else inferAppl isP ps (ResolvedMixTerm i tys [] ps)
                 $ mkTupleTerm ts ps
        ApplTerm t1 t2 ps -> inferAppl isP ps t1 t2
        TupleTerm ts ps -> if null ts then return [(eps, noC, unitType, trm)]
          else do
            ls <- checkList isP (map (const Nothing) ts) ts
            return $ map ( \ (su, cs, tys, trms) ->
              (su, cs, mkProductTypeWithRange tys ps, mkTupleTerm trms ps)) ls
        TypedTerm t qual ty ps -> do
            case qual of
                InType -> do
                    vTy <- freshTypeVar t
                    rs <- infer False t
                    return $ map ( \ (s, cs, typ, tr) ->
                           let sTy = subst s ty in
                               ( s, insertC (Subtyping sTy vTy)
                                     $ insertC (Subtyping typ vTy) cs
                               , unitType, TypedTerm tr qual sTy ps)) rs
                AsType -> do
                    vTy <- freshTypeVar t
                    rs <- infer False t
                    return $ map ( \ (s, cs, typ, tr) ->
                        let sTy = subst s ty in
                                ( s, insertC (Subtyping sTy vTy)
                                       $ insertC (Subtyping typ vTy) cs
                                , sTy, TypedTerm tr qual sTy ps)) rs
                _ -> do
                    let decl = case t of
                          ResolvedMixTerm _ tys ts _
                              | isP && null tys && null ts && qual == OfType
                              -> True
                          _ -> False
                    rs0 <- infer isP t
                    let rs = if decl then rs0 else addSuperType ty rs0
                    return $ map ( \ (s, cs, _, tr) ->
                          let sTy = subst s ty in
                                (s, cs, sTy, case tr of
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
            rs <- fmap (addSuperType unitType) $ infer False t
            putLocalVars vs
            putTypeMap tm
            return $ map ( \ (s, cs, typ, tr) ->
              (s, cs, typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do
            ls <- checkList True (map (const Nothing) pats) pats
            rs <- mapM ( \ ( s, cs, pats, nps) -> do
                       mapM_ (addLocalVar True) $ concatMap extractVars nps
                       es <- infer False resTrm
                       putLocalVars vs
                       return $ map ( \ (s2, cr, rty, rtm) ->
                                      let s3 = compSubst s s2
                                          typ = getFunType (subst s rty)
                                             part $ map (subst s2) pats
                                      in
                                      (s3, joinC (substC s2 cs) $ substC s cr
                                      , typ,
                                       TypedTerm
                                       (LambdaTerm nps part rtm ps)
                                       Inferred typ ps)) es) ls
            return $ concat rs
        CaseTerm ofTrm eqs ps -> do
            ts <- infer False ofTrm
            rty <- freshTypeVar trm
            when (null ts) $ addDiags [mkNiceDiag ga Hint
                                      "unresolved of-term in case" ofTrm]
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
               ts <- infer False inTrm
               return $ map ( \ (s2, cr, ty, nt) ->
                              (compSubst s1 s2,
                               substC s2 cs `joinC` cr,
                               ty, LetTerm br nes nt ps)) ts) es
            putLocalVars vs
            return $ concat rs
        AsPattern (VarDecl v _ ok qs) pat ps -> do
           pats <- infer True pat
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
   pats1 <- inferWithMaybeType True (Just pty) pat >>= reduce
   e <- get
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
       ga = globAnnos e
   if null pats then addDiags [mkNiceDiag ga Hint
                               "unresolved case pattern" pat]
      else return ()
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do
                mapM_ (addLocalVar True) $ extractVars p
                ts <- inferWithMaybeType False (Just $ subst s tty) trm
                  >>= reduce
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

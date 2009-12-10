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
import HasCASL.Builtin
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
import Common.Id
import Common.GlobalAnnotations
import Common.Result
import Common.DocUtils
import Common.Lib.State

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

{- This function has the problem that the type of an earlier component may
   restrict the types of following components too much. -}
checkList :: Bool -> [Maybe Type] -> [Term]
          -> State Env [(Subst, Constraints, [Type], [Term])]
checkList isP mtys trms = case (mtys, trms) of
    (ty : rty, trm : rt) -> do
      fts0 <- inferWithMaybeType isP ty trm
      fts <- reduce True fts0
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
reduceR :: Bool -> Env -> (Subst, Constraints, Type, Term)
        -> State Int (Result (Subst, Constraints, Type, Term))
reduceR doMono te (s, cr, ty, tr) = do
    Result ds0 mc <- shapeRelAndSimplify True te cr
      $ if doMono then Just ty else Nothing
    let ds = map (improveDiag tr) ds0
    return $ case mc of
        Nothing -> Result ds Nothing
        Just (s1, qs) -> let
          s2 = compSubst s s1
          in Result ds $ Just
             (s2, qs, subst s1 ty, substTerm s2 tr)

-- | reduce a substitution
reduce :: Bool -> [(Subst, Constraints, Type, Term)]
       -> State Env [(Subst, Constraints, Type, Term)]
reduce doMono alts = do
       te <- get
       combs <- mapM (\ alt -> do
         Result ds mc <- toEnvState $ reduceR doMono te alt
         addDiags ds
         case mc of
           Nothing -> return []
           Just q -> return [q]) alts
       return $ concat combs

checkForUninstantiatedVars :: GlobalAnnos -> Term -> Range -> State Env ()
checkForUninstantiatedVars ga t p = let
  tys = getAllVarTypes t
  in unless (null tys) $ addDiags
    [(mkDiag Error ("in term '" ++ showGlobalDoc ga t
                    "'\n are uninstantiated type variables")
      $ Set.toList $ Set.unions
      $ map (Set.fromList . freeTVarIds) tys)
     {diagPos = p}]

simplifyTypedTerms :: Env -> Term -> Term
simplifyTypedTerms e = foldTerm mapRec
  { foldTypedTerm = \ _ nt q ty ps ->
      let ntyped = TypedTerm nt q ty ps
          ityped = TypedTerm nt Inferred ty ps
      in case getTypeOf nt of
        Nothing -> ntyped
        Just ty2 -> let isSubT = lesserType e ty2 ty in
          case q of
            InType | isSubT -> unitTerm trueId ps
            _ -> case nt of
              TypedTerm nt2 q2 _ _ ->
                if q2 == AsType && q /= InType && lesserType e ty ty2
                   then TypedTerm nt2 q2 ty ps
                   else if q == AsType && elem q2 [OfType, Inferred] && isSubT
                   then ityped else ntyped
              _ -> if q == AsType && isSubT then ityped else ntyped }

-- | type checking a term
typeCheck :: Type -> Term -> State Env (Maybe Term)
typeCheck exTy trm =
    do alts0 <- inferWithMaybeType False (Just exTy) trm
       alts <- reduce True alts0
       te <- get
       let p = getRange trm
           ga = globAnnos te
       case typeNub te q2p alts of
         [] -> do
           addDiags [mkNiceDiag ga Error "no typing for" trm]
           return Nothing
         [(_, rcs, ty, t)] -> do
           unless (Set.null rcs)
                 $ addDiags [(mkDiag Error ("in term '"
                             ++ showGlobalDoc ga t "' of type '"
                             ++ showDoc ty "'\n unresolved constraints")
                                 rcs){diagPos = p}]
           checkForUninstantiatedVars ga t p
           return $ Just $ simplifyTypedTerms te t
         falts -> do
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
    when (null res) $ addDiags [mkNiceDiag ga Hint ("untypeable term" ++
      case mt of
        Nothing -> ""
        Just ty -> " (with type: "  ++ showGlobalDoc ga ty ")") trm]

-- | infer type of application, consider lifting for lazy types
inferAppl :: Bool -> Range -> Term  -> Term
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl isP ps t1 t2 = do
    ops <- infer isP t1
    warnEmpty Nothing t1 ops
    vs <- gets localVars
    e <- get
    combs <- mapM ( \ (sf, cf, funty, tf) -> do
        (ok, sfty, frty, sub) <- case getTypeAppl funty of
                          (topTy, [paty, prty]) |
                            lesserType e topTy $ toFunType PFunArr ->
                                return (True, Just paty, prty, False)
                          (topTy, [prty]) |
                            lesserType e topTy lazyTypeConstr ->
                                return (True, Just unitType, prty, False)
                          (TypeName _ _ c, []) | c > 0 -> do
                            rty <- freshTypeVar t1
                            return (True, Nothing, rty, True)
                          _ -> return (False, Nothing, funty, False)
        if ok then do
                putLocalVars $ substVarTypes sf vs
                args <- inferWithMaybeType isP sfty t2
                warnEmpty sfty t2 args
                putLocalVars vs
                return $ map ( \ (sa, ca, arty, ta) ->
                        let nTy = subst sa frty in
                          (compSubst sf sa, (if sub then
                               insertC (Subtyping (subst sa funty)
                                $ mkFunArrType arty PFunArr nTy) else id)
                              $ joinC ca $ substC sa cf, nTy,
                            TypedTerm (ApplTerm tf ta ps)
                            Inferred nTy ps)) args
            else return []) ops
    reduce False $ concat combs

getAllVarTypes :: Term -> [Type]
getAllVarTypes = filter (not . null . freeTVars) . getAllTypes

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

-- | efficiently infer type of a monomorphic tuple term
inferWithMaybeType :: Bool -> Maybe Type -> Term
                   -> State Env [(Subst, Constraints, Type, Term)]
inferWithMaybeType isP mt trm = case (trm, mt) of
    (TupleTerm ts@(_ : _ : _) ps, Just ty) -> case getTypeAppl ty of
        (TypeName i _ _, argTys@(_ : _ : _)) | isProductId i ->
          if length ts == length argTys then
              if all (null . freeTVars) argTys then do
                 -- remaining type variables would not become instantiated
                ls <- checkList isP (map Just argTys) ts
                return $ map ( \ (su, cs, tys, trms) ->
                  ( su, cs, mkProductTypeWithRange tys ps
                  , mkTupleTerm trms ps)) ls
              else inferWithMaybeTypeAux isP mt trm
           else return [] -- fail for tuples of different lengths
        _ -> inferWithMaybeTypeAux isP mt trm
    _ -> inferWithMaybeTypeAux isP mt trm

-- | infer type of term (or a pattern if the Bool is True)
inferWithMaybeTypeAux :: Bool -> Maybe Type -> Term
                   -> State Env [(Subst, Constraints, Type, Term)]
inferWithMaybeTypeAux isP mt trm = do
  rs <- infer isP trm
  te <- get
  case mt of
    Nothing -> return rs
    Just inTy -> do
        combs <- mapM (\ q@(s, c, ty, t) -> let nTy = subst s inTy in
            if ty == nTy then return [q] else do
            Result ds mc <- toEnvState $ reduceR False te
              (s, insertC (Subtyping ty nTy) c, nTy, mkTypedTerm t nTy)
            case mc of
              Nothing -> do
                addDiags ds
                return []
              Just alt -> return [alt]) rs
        return $ concat combs

-- | infer type of term (or a pattern if the Bool is True)
infer :: Bool -> Term -> State Env [(Subst, Constraints, Type, Term)]
infer isP trm = do
    e <- get
    let tm = typeMap e
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
          (Just j, pat : rt@(_ : _)) -> case reverse rt of
            lt : ft -> infer isP $ ResolvedMixTerm j tys
                (reverse $ LambdaTerm [pat] Partial lt ps : ft) ps
            [] -> error "ResolvedMixTerm: binder"
          _ ->
            if null ts then case Map.lookup i vs of
               Just (VarDefn t) ->
                 infer isP $ QualVar $ VarDecl i t Other ps
               Nothing -> do
                    insts <- mapM (instOpInfo tys) $ getMinAssumps e i
                    let ls = map ( \ (ty, is, cs, oi) ->
                              (eps, ty, is, cs, oi)) $ catMaybes insts
                    -- possibly fresh variable
                    vl <- if isP && null tys && null ls
                          && (isSimpleId i || i == simpleIdToId uTok) then do
                        vty <- freshTypeVar trm
                        return
                          [(eps, noC, vty, QualVar $ VarDecl i vty Other ps)]
                      else do
                        when (null ls) $
                          addDiags [mkDiag Hint "no type found for" i]
                        return []
                    return $ vl ++ map
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
        TypedTerm t qual ty ps ->
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
                    rs <- inferWithMaybeType isP
                           (if decl then Nothing else Just ty) t
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
            rs <- inferWithMaybeType False (Just $ mkLazyType unitType) t
            putLocalVars vs
            putTypeMap tm
            return $ map ( \ (s, cs, typ, tr) ->
              (s, cs, typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do
            ls <- checkList True (map (const Nothing) pats) pats
            rs <- mapM ( \ ( s, cs, patys, nps) -> do
                       mapM_ (addLocalVar True) $ concatMap extractVars nps
                       es <- infer False resTrm
                       putLocalVars vs
                       return $ map ( \ (s2, cr, rty, rtm) ->
                                      let s3 = compSubst s s2
                                          typ = getFunType (subst s rty)
                                             part $ map (subst s2) patys
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
                           zipWith3 (ProgEq . substTerm sr)
                               pps tts qs)) newTrms) newPats
       putLocalVars vs
       return $ concat combs

inferCaseEq :: Type -> Type -> ProgEq
            -> State Env [(Subst, Constraints, Type, Type, ProgEq)]
inferCaseEq pty tty (ProgEq pat trm ps) = do
   pats1 <- inferWithMaybeType True (Just pty) pat
   e <- get
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
       ga = globAnnos e
   when (null pats)
     $ addDiags [mkNiceDiag ga Hint "unresolved case pattern" pat]
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do
                mapM_ (addLocalVar True) $ extractVars p
                ts <- inferWithMaybeType False (Just $ subst s tty) trm
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

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

module HasCASL.TypeCheck (typeCheck, resolveTerm, getAllTypes) where

import HasCASL.Unify
import HasCASL.AsUtils
import HasCASL.Merge
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.Le
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
import Common.GlobalAnnotations
import Common.Lib.State

import Data.List as List
import Data.Maybe (catMaybes)

import Control.Exception(assert)

substTerm :: Subst -> Term -> Term
substTerm s = mapTerm (id, subst s)

-- | mixfix and type resolution
resolveTerm :: GlobalAnnos -> Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm ga mt trm = do
    mtrm <- resolve ga trm
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
             in return $ Just (subst s t, zip tys $ map (substTypeArg s) tArgs)

instOpInfo :: [Type] -> OpInfo
           -> State Env (Maybe (Type, [Type], Constraints, OpInfo))
instOpInfo tys oi = do
     m <- instantiate tys $ opType oi
     return $ case m of
       Just (ty, cl) ->
           Just (ty, map fst cl, Set.fromList $ map mkConstraint cl, oi)
       Nothing -> Nothing

checkList :: [Maybe Type] -> [Term]
          -> State Env [(Subst, Constraints, [Type], [Term])]
checkList mtys trms = case (mtys, trms) of
    (ty : rty, trm : rt) -> do
      fts <- infer ty trm >>= reduce
      combs <- mapM ( \ (sf, cs, tyf, tf) -> do
                      vs <- gets localVars
                      putLocalVars $ substVarTypes sf vs
                      rts <- checkList (map (fmap (subst sf)) rty) rt
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
                   ms = monoSubsts te
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
    do alts <- infer mt trm >>= reduce
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
                         ("ambiguous typings \n " ++
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
    if null res then addDiags [mkNiceDiag ga Hint ("untypable term" ++
      case mt of
        Nothing -> ""
        Just ty -> " (with type: "  ++ showGlobalDoc ga ty ")\n  ") trm]
      else return ()

-- | infer type of application, consider lifting for lazy types
inferAppl :: Range -> Maybe Type -> Term  -> Term
          -> State Env [(Subst, Constraints, Type, Term)]
inferAppl ps mt t1 t2 = do
    aty <- case t2 of
             TupleTerm [] _ -> return unitType
             _ -> freshTypeVar t2
    rty <- case mt of
             Nothing -> freshTypeVar t1
             Just ty -> return ty
    let mfrty = Just $ mkFunArrType aty PFunArr rty
        mlrty = Just $ TypeAppl lazyTypeConstr rty
    ops <- infer mfrty t1 >>= reduce
    lops <- case t2 of
        TupleTerm [] _ -> do
            laps <- infer mlrty t1 >>= reduce
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
                args <- infer msfty t2 >>= reduce
                warnEmpty msfty t2 args
                putLocalVars vs
                let combs2 = map ( \ (sa, ca, _, ta) ->
                        let sr = compSubst sf sa
                            nTy = subst sa frty in
                          [(sr, joinC ca $ substC sa cf, nTy,
                            TypedTerm (ApplTerm tf ta ps)
                            Inferred nTy ps)]) args
                return $ concat combs2) allOps
        return $ concat combs

getTypeOf :: Term -> Type
getTypeOf trm = case trm of
    TypedTerm _ q t _ -> case q of InType -> unitType
                                   _ -> t
    QualVar (VarDecl _ t _ _) -> t
    QualOp _ _ (TypeScheme [] t _) [] _ -> t
    TupleTerm ts ps -> if null ts then unitType
                       else mkProductTypeWithRange (map getTypeOf ts) ps
    QuantifiedTerm _ _ t _ -> getTypeOf t
    LetTerm _ _ t _ -> getTypeOf t
    AsPattern _ p _ -> getTypeOf p
    _ -> error "getTypeOf"

getAllVarTypes :: Term -> [Type]
getAllVarTypes = filter (not . null . leaves (> 0)) . getAllTypes

getAllTypes :: Term -> [Type]
getAllTypes = foldTerm FoldRec
    { foldQualVar = \ _ (VarDecl _ t _ _) -> [t]
    , foldQualOp = \ _ _ _ _ ts _ -> ts
    , foldApplTerm = \ _ t1 t2 _ -> t1 ++ t2
    , foldTupleTerm = \ _ tts _ -> concat tts
    , foldTypedTerm = \ _ ts _ t _ -> t : ts
    , foldAsPattern = \ _ (VarDecl _ t _ _) ts _ -> t : ts
    , foldQuantifiedTerm = \ _ _ gvs ts _ -> ts ++ concatMap
         ( \ gv -> case gv of
                     GenVarDecl (VarDecl _ t _ _) -> [t]
                     _ -> []) gvs
    , foldLambdaTerm = \ _ _ _ ts _ -> ts
    , foldCaseTerm = \ _ ts tts _ -> concat $ ts : tts
    , foldLetTerm = \ _ _ tts ts _ -> concat $ ts : tts
    , foldResolvedMixTerm = \ _ _ ts tts _ -> ts ++ concat tts
    , foldTermToken = \ _ _ -> []
    , foldMixTypeTerm = \ _ _ _ _ -> []
    , foldMixfixTerm = \ _ tts -> concat tts
    , foldBracketTerm = \ _ _ tts _ -> concat tts
    , foldProgEq = \ _ ps ts _ -> ps ++ ts
    }

-- | infer type of term
infer :: Maybe Type -> Term -> State Env [(Subst, Constraints, Type, Term)]
infer mt trm = do
    e <- get
    let tm = typeMap e
        as = assumps e
        vs = localVars e
        ga = globAnnos e
    case trm of
        qv@(QualVar (VarDecl _ t _ _))  -> return $
            case mt of
                 Nothing -> [(eps, noC, t, qv)]
                 Just ty -> [(eps, insertC (Subtyping t ty) noC, t, qv)]
        QualOp br i sc tys ps -> do
            ms <- instOpInfo tys OpInfo { opType = sc
                                        , opAttrs = Set.empty
                                        , opDefn = NoOpDefn br }
            return $ case ms of
                Nothing -> []
                Just (ty, inst, cs, _) ->
                    let qv = TypedTerm (QualOp br i sc inst ps)
                             Inferred ty ps
                    in [(eps, case mt of
                    Nothing -> cs
                    Just inTy -> insertC (Subtyping ty inTy) cs, ty, qv)]
        ResolvedMixTerm i tys ts ps ->
            if null ts then case Map.lookup i vs of
               Just (VarDefn t) -> infer mt $ QualVar $ VarDecl i t Other ps
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
                    return $ typeNub e q2p $ map
                      ( \ (s, ty, is, cs, oi) ->
                        let od = opDefn oi
                            br = case od of
                                 NoOpDefn v -> v
                                 Definition v _ -> v
                                 _ -> Op
                       in (s, cs, ty, case opType oi of
                           sc@(TypeScheme [] sTy _) -> assert (sTy == ty) $
                                  QualOp br (PolyId i [] ps) sc [] ps
                           sc -> TypedTerm (QualOp br (PolyId i [] ps)
                                            sc is ps)
                                       Inferred ty ps)) ls
            else inferAppl ps mt (ResolvedMixTerm i tys [] ps)
                 $ mkTupleTerm ts ps
        ApplTerm t1 t2 ps -> inferAppl ps mt t1 t2
        TupleTerm ts ps -> if null ts then return
            [(eps, case mt of
              Nothing -> noC
              Just ty -> insertC (Subtyping unitType ty) noC,
              unitType, trm)]
            else do
                ls <- checkList (map (const Nothing) ts) ts
                return $ map ( \ (su, cs, tys, trms) ->
                    let nTy = mkProductTypeWithRange tys ps in
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
                    vTy <- freshTypeVar t
                    rs <- infer Nothing t
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
                    rs <- infer Nothing t
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
                    rs <- infer (Just ty) t
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
            rs <- infer (Just unitType) t
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
            ls <- checkList (map Just pvs) pats
            rs <- mapM ( \ ( s, cs, _, nps) -> do
                       mapM_ (addLocalVar True) $ concatMap extractVars nps
                       es <- infer (Just $ subst s rty) resTrm
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
            ts <- infer Nothing ofTrm
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
               ts <- infer mt inTrm
               return $ map ( \ (s2, cr, ty, nt) ->
                              (compSubst s1 s2,
                               substC s2 cs `joinC` cr,
                               ty, assert (getTypeOf nt == ty) $
                               LetTerm br nes nt ps)) ts) es
            putLocalVars vs
            return $ concat rs
        AsPattern (VarDecl v _ ok qs) pat ps -> do
           pats <- infer mt pat
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
       newPats <- checkList (map (const Nothing) pats) pats
       combs <- mapM ( \ (sf, pcs, tys, pps) -> do
             mapM_ (addLocalVar True) $ concatMap extractVars pps
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
   pats1 <- infer (Just pty) pat >>= reduce
   e <- get
   let pats = filter ( \ (_, _, _, p) -> isPat e p) pats1
       ga = globAnnos e
   if null pats then addDiags [mkNiceDiag ga Hint
                               "unresolved case pattern" pat]
      else return ()
   vs <- gets localVars
   es <- mapM ( \ (s, cs, ty, p) -> do
                mapM_ (addLocalVar True) $ extractVars p
                ts <- infer (Just $  subst s tty) trm >>= reduce
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

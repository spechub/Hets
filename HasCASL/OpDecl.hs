{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

analyse operation declarations
-}

module HasCASL.OpDecl where

import Data.Maybe

import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import Common.Result
import Common.GlobalAnnotations

import HasCASL.As
import HasCASL.TypeAna
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.AsUtils
import HasCASL.MixAna
import HasCASL.TypeCheck
import HasCASL.ProgEq

anaAttr :: GlobalAnnos -> TypeScheme -> OpAttr -> State Env (Maybe OpAttr)
anaAttr ga (TypeScheme tvs ty _) (UnitOpAttr trm ps) =
    do e <- get
       let mTy = let (fty, fArgs) = getTypeAppl ty in case fArgs of
                   [arg, t3] | lesserType e fty (toType $ arrowId PFunArr)
                       -> let (pty, ts) = getTypeAppl arg in case ts of
                          [t1, t2] | lesserType e pty (toType $ productId 2)
                                       -> Just (t1,t2,t3)
                          _ -> Nothing
                   _ -> Nothing
       let tm = typeMap e
       mapM_ (addTypeVarDecl False) tvs
       case mTy of
             Nothing -> do addDiags [mkDiag Error
                                     "unexpected type of operation" ty]
                           mt <- resolveTerm ga Nothing trm
                           putTypeMap tm
                           case mt of
                                   Nothing -> return Nothing
                                   Just t  -> return $ Just $ UnitOpAttr t ps
             Just (t1, t2, t3) ->
                 do if t1 == t2 && t2 == t3 then
                       return ()
                       else addDiags [mkDiag Error
                                 "unexpected type components of operation" ty]
                    mt <- resolveTerm ga (Just t3) trm
                    putTypeMap tm
                    case mt of Nothing -> return Nothing
                               Just t -> return $ Just $ UnitOpAttr t ps
anaAttr _ _ b = return $ Just b

tuplePatternToType :: [VarDecl] -> Type
tuplePatternToType vds = mkProductType (map ( \ (VarDecl _ t _ _) -> t) vds)

getUninstOpId :: TypeScheme -> OpId -> (OpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args qs) =
      (OpId i [] qs, TypeScheme (args ++ tvs) q ps)

anaOpId :: GlobalAnnos -> OpBrand -> TypeScheme -> [OpAttr] -> OpId
        -> State Env Bool
anaOpId ga br partSc attrs o =
    do let (OpId i _ _, sc) = getUninstOpId partSc o
       mSc <- anaTypeScheme sc
       case mSc of
           Nothing -> return False
           Just newSc -> do
               mAttrs <- mapM (anaAttr ga newSc) attrs
               addOpId i newSc (catMaybes mAttrs) $ NoOpDefn br

anaOpItem :: GlobalAnnos -> OpBrand -> OpItem -> State Env (Maybe OpItem)
anaOpItem ga br (OpDecl is sc attr ps) = do
        bs <- mapM (anaOpId ga br sc attr) is
        let us = map fst $ filter snd $ zip is bs
        return $ if null us then Nothing else
            Just $ OpDecl us sc attr ps

anaOpItem ga br (OpDefn o oldPats sc partial trm ps) =
    do let (OpId i _ _, TypeScheme tArgs scTy qs) = getUninstOpId sc o
       checkUniqueVars $ concat oldPats
       tvs <- gets localTypeVars
       mArgs <- mapM anaddTypeVarDecl tArgs
       mPats <- mapM (mapM anaVarDecl) oldPats
       let newPats = map catMaybes mPats
           monoPats = map (map makeMonomorph) newPats
           pats = map (\ l -> mkTupleTerm (map QualVar l) nullRange) monoPats
       vs <- gets localVars
       mapM_ (mapM_ $ addLocalVar True) monoPats
       let newArgs = catMaybes mArgs
       mty <- anaStarType scTy
       mtrm <- resolve ga trm
       case (mty, mtrm) of
           (Just ty, Just rTrm) -> do
               mt <- typeCheck Nothing $ TypedTerm rTrm AsType (monoType ty) ps
               newSc <- generalizeS $ TypeScheme newArgs
                      (getFunType ty partial
                       $ map tuplePatternToType newPats) qs
               putLocalVars vs
               putLocalTypeVars tvs
               case mt of
                   Just lastTrm -> do
                       let lamTrm = case (pats, partial) of
                                    ([], Total) -> lastTrm
                                    _ -> LambdaTerm pats partial lastTrm ps
                           ot = QualOp br (InstOpId i [] nullRange)
                                newSc nullRange
                           lhs = mkApplTerm ot pats
                           ef = mkEqTerm eqId ps lhs lastTrm
                           f = mkForall (map GenTypeVarDecl newArgs
                                          ++ (map GenVarDecl $
                                              concatMap extractVars pats)) ef
                       addOpId i newSc [] $ Definition br lamTrm
                       appendSentences [makeNamed ("def_" ++ showId i "")
                                       $ Formula f]
                       return $ Just $ OpDefn o oldPats sc partial rTrm ps
                   Nothing -> do
                       addOpId i newSc [] $ NoOpDefn br
                       return $ Just $ OpDecl [OpId i [] ps] newSc [] ps
           _ -> do
               putLocalVars vs
               putLocalTypeVars tvs
               return Nothing

-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env (Maybe ProgEq)
anaProgEq ga pe@(ProgEq _ _ q) =
    do rp <- resolve ga (LetTerm Program [pe] (BracketTerm Parens [] q) q)
       case rp of
         Just t@(LetTerm _ (rpe@(ProgEq _ _ _) : _) _ _) -> do
           mp <- typeCheck Nothing t
           case mp of
             Just (LetTerm _ (newPrg@(ProgEq newPat _ _) : _) _ _) ->
               case getAppl newPat of
               Just (i, sc, _) -> do
                           addOpId i sc [] $ NoOpDefn Op
                           appendSentences [(makeNamed ("pe_" ++ showId i "")
                                            $ ProgEqSen i sc newPrg)
                                            { isDef   = True }]
                           e <- get
                           if isLHS e newPat then return ()
                              else addDiags [mkNiceDiag ga Warning
                                         "illegal lhs pattern"
                                         newPat]
                           return $ Just rpe
               Nothing -> do addDiags [mkNiceDiag ga Error
                                         "illegal toplevel pattern"
                                         newPat]
                             return Nothing
             _ -> return Nothing
         _ -> return Nothing

getApplConstr :: Pattern -> (Pattern, [Pattern])
getApplConstr pat =
    case pat of
    ApplTerm p1 p2 _ ->
        let (tp, args) = getApplConstr p1 in (tp, p2:args)
    TypedTerm tp _ _ _ -> getApplConstr tp
    _ -> (pat, [])





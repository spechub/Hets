{- |
Module      :  $Header$
Description :  analyse operation declarations
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

analyse operation declarations
-}

module HasCASL.OpDecl
  ( anaOpItem
  , anaProgEq
  ) where

import Data.Maybe (catMaybes)
import qualified Data.Set as Set

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
anaAttr ga (TypeScheme tvs ty _) b = case b of
    UnitOpAttr trm ps -> do
       e <- get
       let mTy = let (fty, fArgs) = getTypeAppl ty in case fArgs of
                   [arg, t3] | lesserType e fty (toFunType PFunArr)
                       -> let (pty, ts) = getTypeAppl arg in case ts of
                          [t1, t2] | lesserType e pty (toProdType 2 ps)
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
                 do if t1 == t2 && t2 == t3 then return ()
                       else addDiags [mkDiag Error
                                 "unexpected type components of operation" ty]
                    mt <- resolveTerm ga (Just t3) trm
                    putTypeMap tm
                    case mt of Nothing -> return Nothing
                               Just t -> return $ Just $ UnitOpAttr t ps
    _ -> return $ Just b

tuplePatternToType :: [VarDecl] -> Type
tuplePatternToType vds =
    mkProductTypeWithRange (map ( \ (VarDecl _ t _ _) -> t) vds) $ posOf vds

anaOpId :: GlobalAnnos -> OpBrand -> TypeScheme -> [OpAttr] -> Id
        -> State Env Bool
anaOpId ga br sc attrs i =
    do mSc <- anaPolyId i sc
       case mSc of
           Nothing -> return False
           Just (j, newSc) -> do
               mAttrs <- mapM (anaAttr ga newSc) attrs
               addOpId j newSc (Set.fromList $ catMaybes mAttrs) $ NoOpDefn br

-- | analyse an op-item
anaOpItem :: GlobalAnnos -> OpBrand -> OpItem -> State Env (Maybe OpItem)
anaOpItem ga br oi = case oi of
    OpDecl is sc attr ps -> do
        bs <- mapM (anaOpId ga br sc attr) is
        let us = map fst $ filter snd $ zip is bs
        return $ if null us then Nothing else
            Just $ OpDecl us sc attr ps
    OpDefn i oldPats sc@(TypeScheme tArgs scTy qs) trm ps
        -> do
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
           (Just rty, Just rTrm) -> do
               let (partial, ty) = case getTypeAppl rty of
                     (TypeName j _ _ , [lt]) | j == lazyTypeId -> (Partial, lt)
                     _ -> (Total, rty)
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
                           ot = QualOp br i newSc [] nullRange
                           lhs = mkApplTerm ot pats
                           ef = mkEqTerm eqId ps lhs lastTrm
                           f = mkForall (map GenTypeVarDecl newArgs
                                          ++ (map GenVarDecl $
                                              concatMap extractVars pats)) ef
                       addOpId i newSc Set.empty $ Definition br lamTrm
                       appendSentences [makeNamed ("def_" ++ showId i "")
                                       $ Formula f]
                       return $ Just $ OpDefn i oldPats sc rTrm ps
                   Nothing -> do
                       addOpId i newSc Set.empty $ NoOpDefn br
                       return $ Just $ OpDecl [i] newSc [] ps
           _ -> do
               putLocalVars vs
               putLocalTypeVars tvs
               return Nothing

-- | analyse a program equation
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
                           addOpId i sc Set.empty $ NoOpDefn Op
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

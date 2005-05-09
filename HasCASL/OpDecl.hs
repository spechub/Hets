{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.AsUtils
import HasCASL.MinType
import HasCASL.TypeCheck
import HasCASL.ProgEq

anaAttr :: GlobalAnnos -> TypeScheme -> OpAttr -> State Env (Maybe OpAttr)
anaAttr ga (TypeScheme tvs ty _) (UnitOpAttr trm ps) = 
    do let mTy = case unalias ty of 
                      FunType arg _ t3 _ -> 
                          case unalias arg of 
                          ProductType [t1, t2] _ -> Just (t1,t2,t3)
                          _ -> Nothing
                      _ -> Nothing
       tm <- gets typeMap
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

patternsToType :: [[VarDecl]] -> Type -> Type
patternsToType [] t = t
patternsToType (p: ps) t = FunType (tuplePatternToType p) PFunArr 
                          (patternsToType ps t) []

tuplePatternToType :: [VarDecl] -> Type
tuplePatternToType vds = mkProductType (map ( \ (VarDecl _ t _ _) -> t) vds) []

getUninstOpId :: TypeScheme -> OpId -> (OpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args qs) =
      (OpId i [] qs, TypeScheme (args ++ tvs) q ps)  

anaOpId :: GlobalAnnos -> OpBrand -> TypeScheme -> [OpAttr] -> OpId 
        -> State Env (Maybe OpId) 
anaOpId ga br partSc attrs o =
    do let (OpId i _ _, sc) = getUninstOpId partSc o
       mSc <- anaTypeScheme sc 
       case mSc of 
           Nothing -> return Nothing
           Just newSc -> do
               mAttrs <- mapM (anaAttr ga newSc) attrs
               mo <- addOpId i newSc (catMaybes mAttrs) $ NoOpDefn br 
               return $ fmap (const o) mo

anaOpItem :: GlobalAnnos -> OpBrand -> OpItem -> State Env (Maybe OpItem)
anaOpItem ga br (OpDecl is sc attr ps) = do
        mus <- mapM (anaOpId ga br sc attr) is
        let us = catMaybes mus
        return $ if null us then Nothing else
            Just $ OpDecl us sc attr ps

anaOpItem ga br (OpDefn o oldPats sc partial trm ps) = 
    do let (op@(OpId i _ _), TypeScheme tArgs scTy qs) = 
               getUninstOpId sc o
       checkUniqueVars $ concat oldPats
       tm <- gets typeMap
       ass <- gets assumps
       mArgs <- mapM anaTypeVarDecl tArgs
       mPats <- mapM (mapM anaVarDecl) oldPats
       putAssumps ass
       let newPats = map catMaybes mPats
           monoPats = map (map makeMonomorph) newPats
           pats = map (\ l -> mkTupleTerm (map QualVar l) []) monoPats
       vs <- gets localVars
       mapM (mapM addLocalVar) monoPats
       let newArgs = catMaybes mArgs  
       mty <- anaStarType scTy
       case mty of 
           Just ty -> do 
               mt <- resolveTerm ga Nothing $ TypedTerm trm AsType ty ps
               putLocalVars vs
               putTypeMap tm
               newSc <- generalizeS $ TypeScheme newArgs 
                      (patternsToType newPats ty) qs
               case mt of 
                   Just lastTrm -> do 
                       let lamTrm = case (pats, partial) of 
                                    ([], Total) -> lastTrm
                                    _ -> LambdaTerm pats partial lastTrm ps
                           ot = QualOp br (InstOpId i [] []) newSc []
                           lhs = mkApplTerm ot pats
                           ef = mkEqTerm eqId ps lhs lastTrm
                           f = mkForall (map GenTypeVarDecl newArgs
                                          ++ (map GenVarDecl $ 
                                              concatMap extractVars pats)) ef
                       addOpId i newSc [] $ Definition br lamTrm
                       appendSentences [NamedSen 
                                                   ("def_" ++ showId i "")
                                                   $ Formula f] 
                       return $ Just $ OpDefn op [] newSc Total lamTrm ps
                   Nothing -> do 
                       addOpId i newSc [] $ NoOpDefn br
                       return $ Just $ OpDecl [OpId i [] ps] newSc [] ps
           Nothing -> do 
               resolveTerm ga Nothing trm -- get a view more diags
               putLocalVars vs
               putTypeMap tm
               return Nothing
                                                          
-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env (Maybe ProgEq)
anaProgEq ga pe@(ProgEq _ _ q) =
    do mp <- resolveTerm ga Nothing (LetTerm Program [pe] 
                                     (BracketTerm Parens [] q) q)
       case mp of 
           Just (LetTerm _ (newPrg@(ProgEq newPat _ _) : _) _ _) -> 
               case getAppl newPat of
               Just (i, sc, _) -> do 
                           addOpId i sc [] $ NoOpDefn Op
                           appendSentences [NamedSen ("pe_" ++ showId i "")
                                            $ ProgEqSen i sc newPrg]
                           e <- get
                           if isLHS e newPat then return () 
                              else addDiags [mkDiag Warning
                                         "illegal lhs pattern"
                                         newPat]
                           return $ Just newPrg
               Nothing -> do addDiags [mkDiag Error 
                                         "illegal toplevel pattern"
                                         newPat]
                             return Nothing
           _ -> return Nothing

getApplConstr :: Pattern -> (Pattern, [Pattern])
getApplConstr pat = 
    case pat of 
    ApplTerm p1 p2 _ -> 
        let (tp, args) = getApplConstr p1 in (tp, p2:args)
    TypedTerm tp _ _ _ -> getApplConstr tp
    _ -> (pat, [])
                           




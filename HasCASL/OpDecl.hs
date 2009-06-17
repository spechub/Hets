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
  , mkEnvForall
  ) where

import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec (parse, eof)
import Control.Monad

import Common.Id
import Common.AS_Annotation
import Common.Lib.State as State
import Common.Result
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Doc
import Common.Lexer ((<<), skip)

import HasCASL.As
import HasCASL.HToken
import HasCASL.TypeAna
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.AsUtils
import HasCASL.MixAna
import HasCASL.TypeCheck
import HasCASL.ProgEq

anaAttr :: TypeScheme -> OpAttr -> State Env (Maybe OpAttr)
anaAttr (TypeScheme tvs ty _) b = case b of
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
                           putTypeMap tm
                           return Nothing
             Just (t1, t2, t3) ->
                 do if t1 == t2 && t2 == t3 then return ()
                       else addDiags [mkDiag Error
                                 "unexpected type components of operation" ty]
                    mt <- resolveTerm t3 trm
                    putTypeMap tm
                    case mt of Nothing -> return Nothing
                               Just t -> return $ Just $ UnitOpAttr t ps
    _ -> return $ Just b

tuplePatternToType :: [VarDecl] -> Type
tuplePatternToType vds =
    mkProductTypeWithRange (map ( \ (VarDecl _ t _ _) -> t) vds) $ getRange vds

anaOpId :: OpBrand -> TypeScheme -> [OpAttr] -> PolyId -> State Env Bool
anaOpId br sc attrs i@(PolyId j _ _) =
    do mSc <- anaPolyId i sc
       case mSc of
           Nothing -> return False
           Just newSc -> do
               mAttrs <- mapM (anaAttr newSc) attrs
               addOpId j newSc (Set.fromList $ catMaybes mAttrs) $ NoOpDefn br

-- | analyse an op-item
anaOpItem :: OpBrand -> Annoted OpItem -> State Env (Annoted (Maybe OpItem))
anaOpItem br oi = do
  let Result ds (Just bs) = extractBinders $ l_annos oi ++ r_annos oi
  addDiags ds
  case item oi of
    OpDecl is sc attr ps -> do
        case is of
          [PolyId i _ _] -> mapM_ (addBinder i) bs
          _ -> unless (null bs) $ addDiags
            [mkDiag Warning "ignoring binder syntax" bs]
        ois <- mapM (anaOpId br sc attr) is
        let us = map fst $ filter snd $ zip is ois
        return $ replaceAnnoted (if null us then Nothing else
            Just $ OpDecl us sc attr ps) oi
    OpDefn p@(PolyId i _ _) oldPats rsc@(TypeScheme tArgs scTy qs) trm ps
        -> do
       mapM_ (addBinder i) bs
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
       mtrm <- resolve trm
       case (mty, mtrm) of
           (Just rty, Just rTrm) -> do
               let (partial, ty) = case getTypeAppl rty of
                     (TypeName j _ _ , [lt]) | j == lazyTypeId -> (Partial, lt)
                     _ -> (Total, rty)
                   monoty = monoType ty
               mt <- typeCheck monoty $ TypedTerm rTrm AsType monoty ps
               e <- get
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
                           ot = QualOp br p newSc [] Infer
                             nullRange
                           lhs = mkApplTerm ot pats
                           ef = mkEqTerm eqId monoty ps lhs lastTrm
                           f = mkEnvForall e ef ps
                       addOpId i newSc Set.empty $ Definition br lamTrm
                       appendSentences
                           [(makeNamed (getRLabel oi) $ Formula f)
                            { isDef = True }]
                       return $ replaceAnnoted
                         (Just $ OpDefn p oldPats rsc rTrm ps) oi
                   Nothing -> do
                       addOpId i newSc Set.empty $ NoOpDefn br
                       return $ replaceAnnoted
                         (Just $ OpDecl [p] newSc [] ps) oi
           _ -> do
               putLocalVars vs
               putLocalTypeVars tvs
               return $ replaceAnnoted Nothing oi

-- | analyse a program equation
anaProgEq :: Annoted ProgEq -> State Env (Maybe ProgEq)
anaProgEq ape = do
       let pe@(ProgEq _ _ q) = item ape
       rp <- resolve (LetTerm Program [pe] (BracketTerm Parens [] q) q)
       case rp of
         Just t@(LetTerm _ (rpe@(ProgEq _ _ _) : _) _ _) -> do
           mp <- typeCheck unitType t
           ga <- State.gets globAnnos
           case mp of
             Just (LetTerm _ (newPrg@(ProgEq newPat _ _) : _) _ _) ->
               case getAppl newPat of
               Just (i, sc, _) -> do
                           addOpId i sc Set.empty $ NoOpDefn Op
                           appendSentences [(makeNamed ("pe_" ++ showId i "")
                                            $ ProgEqSen i sc newPrg)
                                            { isDef = True }]
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
extractBinderId :: Annotation -> Result Id
extractBinderId a = case a of
  Unparsed_anno (Annote_word f@"binder") s r ->
    case parse (skip >> opId << eof) f $ fromAText s of
      Right i -> return i
      Left err -> fatal_error (showErr err ++ "\nin " ++ show (annoDoc a)) r
  _ -> Result [] Nothing

extractBinders :: [Annotation] -> Result [Id]
extractBinders as =
    let rs = map extractBinderId as
        ds = concatMap diags rs
    in if null ds then return $ catMaybes $ map maybeResult rs
       else Result ds $ Just []

addBinding :: Id -> Id -> State.State Env ()
addBinding o b = do
  addDiags $ getBinderDiags o b
  State.modify $ \ e -> e { binders = Map.insert b o $ binders e }
  e <- State.get
  let ga = globAnnos e
      aa = assoc_annos ga
  when (isInfix b && not (Map.member b aa)) $
      State.put e { globAnnos = ga { assoc_annos = Map.insert b ARight aa }}

getBinderDiags :: Id -> Id -> [Diagnosis]
getBinderDiags o b =
    let c = placeCount b
        d = placeCount o + 1
        str = "expected " ++ show (max 2 d) ++ " places in binder"
    in if c < 2 then [mkDiag Error str b]
    else if d /= c then
       if isMixfix o then [mkDiag Warning str b]
       else [mkDiag Hint ("non-mixfix-id '" ++ show o ++ "' for binder") b]
    else []

addBinder :: Id -> Id -> State.State Env ()
addBinder o b = do
  bs <- State.gets binders
  as <- State.gets assumps
  when (Map.member b as) $ addDiags
    [mkDiag Warning "binder shadows shadows global name(s)" b]
  case Map.lookup b bs of
    Just o2 -> if o == o2 then do
        addDiags [Diag Warning
                  ("binder conflict for: " ++ show b ++ expected o2 o)
                  $ posOfId b]
        addBinding o b
      else addDiags [mkDiag Warning "repeated binder syntax" b]
    Nothing -> addBinding o b

fromAText :: Annote_text -> String
fromAText t = case t of
  Line_anno s -> s
  Group_anno l -> unlines l

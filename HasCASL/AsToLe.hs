{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   conversion from As to Le
-}

module HasCASL.AsToLe where

import Common.AS_Annotation
import HasCASL.As
import HasCASL.ClassAna
import HasCASL.ClassDecl
import Common.GlobalAnnotations
import Common.Id
import qualified Common.Lib.Set as Set
import HasCASL.Le
import Data.Maybe
import Common.Lib.State
import Common.Named
import Common.Result
import Common.PrettyPrint
import HasCASL.OpDecl
import HasCASL.TypeDecl
import HasCASL.MixAna
import HasCASL.Reader

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

missingAna :: PrettyPrint a => a -> [Pos] -> State Env ()
missingAna t ps = appendDiags [Diag FatalError 
			       ("no analysis yet for: " ++ showPretty t "")
			      $ if null ps then nullPos else head ps]

anaBasicSpec :: GlobalAnnos -> BasicSpec -> State Env ()
anaBasicSpec ga (BasicSpec l) = mapM_ (anaBasicItem ga) $ map item l

anaBasicItem :: GlobalAnnos -> BasicItem -> State Env ()
anaBasicItem ga (SigItems i) = anaSigItems ga Loose i
anaBasicItem ga (ClassItems inst l _) = mapM_ (anaAnnotedClassItem ga inst) l
anaBasicItem _ (GenVarItems l _) = mapM_ anaGenVarDecl l
anaBasicItem ga (ProgItems l _) = mapM_ (anaProgEq ga) $ map item l
anaBasicItem _ (FreeDatatype l _) = mapM_ (anaDatatype Free Plain) $ map item l
anaBasicItem ga (GenItems l _) = mapM_ (anaSigItems ga Generated) $ map item l
anaBasicItem ga (AxiomItems decls fs _) = 
    do tm <- gets typeMap -- save type map
       as <- gets assumps -- save vars
       mapM_ anaGenVarDecl decls
       ds <- mapM (( \ (TermFormula t) -> 
		     toRResultState $ resolveTerm ga logicalType t ) . item) fs
       putTypeMap tm -- restore 
       putAssumps as -- restore
       appendDiags $ concatMap diags ds
       let sens = concat $ zipWith ( \ r f -> 
			    case maybeResult r of 
			    Just t -> [NamedSen (getRLabel f) $ TermFormula t]
			    Nothing -> [] ) ds fs
       appendSentences sens

appendSentences :: [Named Formula] -> State Env ()
appendSentences fs =
    if null fs then return () else
    do e <- get
       put $ e {sentences = sentences e ++ fs}

anaSigItems :: GlobalAnnos -> GenKind -> SigItems -> State Env ()
anaSigItems _ gk (TypeItems inst l _) = 
    mapM_ (anaTypeItem gk inst) $ map item l
anaSigItems ga _ (OpItems l _) =  mapM_ (anaOpItem ga) $ map item l

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

anaGenVarDecl :: GenVarDecl -> State Env ()
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeVarDecl t

convertTypeToClass :: Type -> ReadR ClassMap Class
convertTypeToClass (TypeToken t) = 
       if tokStr t == "Type" then return universe else do
          let ci = simpleIdToId t
          mapReadR ( \ (Result _ m) -> 
              case m of 
		     Just _ -> Result [] (Just $ Intersection 
					      (Set.single ci) [])
                     Nothing -> Result 
				    [mkDiag Hint "not a class" ci] Nothing )
	      $ anaClassId ci

convertTypeToClass (BracketType Parens ts ps) = 
       do cs <- mapM convertTypeToClass ts
	  return $ Intersection (Set.unions $ map iclass cs) ps

convertTypeToClass t = lift $ Result [mkDiag Hint "not a class" t] Nothing

convertTypeToKind :: Type -> ReadR ClassMap Kind

convertTypeToKind (FunType t1 FunArr t2 ps) = 
    do k1 <- convertTypeToKind t1
       k2 <- convertTypeToKind t2
       return $ KindAppl k1 k2 ps

convertTypeToKind (BracketType Parens [t] _) = 
    do k <- convertTypeToKind t
       return $ k

convertTypeToKind (MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> lift $ Result [] Nothing
	      _ -> do k1 <- convertTypeToClass t1
		      return $ ExtClass k1 v [tokPos t]

convertTypeToKind t = 
    do c <-  convertTypeToClass t
       return $ ExtClass c InVar []

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t s q) = 
    if isSimpleId v then
       do mc <- toMaybeState classMap $ convertTypeToKind t 
	  case mc of
	       Just c -> anaTypeVarDecl(TypeArg v c s q)
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ _) = 
		   do (k, t) <- anaTypeS (star, oldT)
		      checkKindsS v star k
		      addOpId v (simpleTypeScheme t) [] VarDefn

-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: GlobalAnnos -> Instance -> Annoted ClassItem 
		    -> State Env ()
anaAnnotedClassItem ga _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ (anaBasicItem ga) $ map item l

-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env ()
anaProgEq ga (ProgEq pat trm _) =
    do Result es mp <- toRResultState $ resolvePattern ga pat
       appendDiags es
       case mp of 
	   Nothing -> return ()
	   Just (ty, newPat) -> do
	       let bs = extractBindings newPat
	       e <- get
	       mapM_ anaVarDecl bs
	       Result ts mt <- toRResultState $ resolveTerm ga ty trm
	       put e
	       appendDiags ts
	       case mt of 
		   Nothing -> return ()
		   Just newTerm -> 
		       case removeResultType newPat of
		       PatternConstr (InstOpId i _tys _) sc args ps ->
				addOpId i sc [] $ Definition $ 
					if null args then newTerm
					else LambdaTerm args Partial newTerm ps
		       _ -> appendDiags $ [mkDiag Error 
					   "no toplevel pattern" newPat]
		       where removeResultType p = 
				 case p of 
				 TypedPattern tp _ _ -> 
				     removeResultType tp
				 _ -> p


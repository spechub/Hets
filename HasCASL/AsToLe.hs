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
import HasCASL.TypeAna
import HasCASL.TypeDecl
import HasCASL.MixAna

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

missingAna :: PrettyPrint a => a -> [Pos] -> State Env ()
missingAna t ps = addDiags [Diag FatalError 
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
       ts <- mapM (( \ (TermFormula t) -> 
		     resolveTerm ga logicalType t ) . item) fs
       putTypeMap tm -- restore 
       putAssumps as -- restore
       let sens = concat $ zipWith ( \ mt f -> 
			    case mt of 
			    Nothing -> []
			    Just t -> [NamedSen (getRLabel f) $ TermFormula t])
		  ts fs
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

convertTypeToClass :: Type -> State Env (Maybe Class)
convertTypeToClass (TypeToken t) = 
       if tokStr t == "Type" then return $ Just universe else do
          let ci = simpleIdToId t
	  e <- get					       
	  mk <- anaClassId ci
	  case mk of 
		  Nothing -> do put e
				addDiags [mkDiag Hint "not a class" ci]
				return Nothing
		  _ -> return $ Just $ Intersection  (Set.single ci) []
convertTypeToClass (BracketType Parens ts ps) = 
       do cs <- mapM convertTypeToClass ts
	  if all isJust cs then 
	     return $ Just $ Intersection (Set.unions $ map iclass $ 
				    catMaybes cs) ps
	     else return Nothing

convertTypeToClass t = 
    do addDiags [mkDiag Hint "not a class" t]
       return Nothing

convertTypeToKind :: Type -> State Env (Maybe Kind)
convertTypeToKind (FunType t1 FunArr t2 ps) = 
    do mk1 <- convertTypeToKind t1
       mk2 <- convertTypeToKind t2
       case (mk1, mk2) of
           (Just k1, Just k2) -> return $ Just $ KindAppl k1 k2 ps
	   _ -> return Nothing

convertTypeToKind (BracketType Parens [t] _) = 
    do convertTypeToKind t

convertTypeToKind ty@(MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> do addDiags [mkDiag Hint "no kind" ty]
			  return Nothing
	      _ -> do mk1 <- convertTypeToClass t1
		      case mk1 of 
			  Just k1 -> return $ Just $ ExtClass k1 v [tokPos t]
			  _ -> return Nothing
convertTypeToKind t = 
    do mc <- convertTypeToClass t
       return $ fmap ( \ c -> ExtClass c InVar []) mc

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t s q) = 
    if isSimpleId v then
    do mk <- convertTypeToKind t
       case mk of 
	   Just k -> anaTypeVarDecl(TypeArg v k s q)
           _ -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ _) = 
		   do mt <- anaStarType oldT
		      case mt of 
		          Nothing -> return ()
			  Just t -> addOpId v (simpleTypeScheme t) [] VarDefn

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
    do mp <- resolvePattern ga pat
       case mp of 
	   Nothing -> return ()
	   Just (ty, newPat) -> do
	       let bs = extractBindings newPat
	       e <- get
	       mapM_ anaVarDecl bs
	       mt <- resolveTerm ga ty trm
	       put e
	       case mt of 
		   Nothing -> return ()
		   Just newTerm ->case removeResultType newPat of
		       PatternConstr (InstOpId i _tys _) sc args ps ->
				addOpId i sc [] $ Definition $ 
					if null args then newTerm
					else LambdaTerm args Partial newTerm ps
		       _ -> addDiags $ [mkDiag Error 
					   "no toplevel pattern" newPat]
		       where removeResultType p = 
				 case p of 
				 TypedPattern tp _ _ -> 
				     removeResultType tp
				 _ -> p



{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module HasCASL.AsToLe where

import Common.AS_Annotation
import HasCASL.As
import HasCASL.ClassAna
import HasCASL.ClassDecl
import Common.Id
import qualified Common.Lib.Set as Set
import HasCASL.Le
import Common.Lexer 
import Data.Maybe
import Control.Monad
import Common.Lib.State
import HasCASL.OpDecl
import Common.Result
import Common.PrettyPrint
import HasCASL.PrintAs
import HasCASL.TypeAna
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

anaBasicSpec :: BasicSpec -> State Env ()
anaBasicSpec (BasicSpec l) = mapM_ anaBasicItem $ map item l

anaBasicItem :: BasicItem -> State Env ()
anaBasicItem (SigItems i) = anaSigItems Loose i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaBasicItem t@(ProgItems _ p) = missingAna t p
anaBasicItem (FreeDatatype l _) = mapM_ (anaDatatype Free Plain) $ map item l
anaBasicItem (GenItems l _) = mapM_ (anaSigItems Generated) $ map item l
anaBasicItem (AxiomItems decls fs _) = 
    do tm <- gets typeMap -- save type map
       as <- gets assumps -- save vars
       mapM_ anaGenVarDecl decls
       ds <- mapM (( \ (TermFormula t) -> resolveTerm t ) . item) fs
       appendDiags $ concatMap diags ds
       putTypeMap tm -- restore 
       putAssumps as -- restore
       -- store the formulae

anaSigItems :: GenKind -> SigItems -> State Env ()
anaSigItems gk (TypeItems inst l _) = mapM_ (anaTypeItem gk inst) $ map item l
anaSigItems _ (OpItems l _) =  mapM_ anaOpItem $ map item l
anaSigItems _ l@(PredItems _ p) = missingAna l p 

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

anaGenVarDecl :: GenVarDecl -> State Env ()
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeVarDecl t

isSimpleId :: Id -> Bool
isSimpleId (Id ts _ _) = null (tail ts) && head (tokStr (head ts)) 
			 `elem` caslLetters

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
		      checkKindsS (posOfId v) k star
		      addOpId v (simpleTypeScheme t) [] VarDefn

-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaBasicItem $ map item l


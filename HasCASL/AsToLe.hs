
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
import Control.Monad.State
import HasCASL.OpDecl
import Common.Result
import Common.PrettyPrint
import HasCASL.PrintAs
import HasCASL.TypeAna
import HasCASL.TypeDecl
import HasCASL.MixAna

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
    do tm <- getTypeMap -- save type map
       as <- getAssumps -- save vars
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

convertTypeToClass :: ClassMap -> Type -> Result Class
convertTypeToClass cMap (TypeToken t) = 
       if tokStr t == "Type" then Result [] (Just $ universe) else 
          let ci = simpleIdToId t
              ds = anaClassId cMap ci
              in case ds of 
			 Just _ -> Result [] (Just $ Intersection 
					      (Set.single ci) [])
                         Nothing -> Result 
				    [mkDiag Hint "not a class" ci] Nothing

convertTypeToClass cMap (BracketType Parens ts ps) = 
       do cs <- mapM (convertTypeToClass cMap) ts
	  return $ Intersection (Set.unions $ map iclass cs) ps

convertTypeToClass _ t = Result [mkDiag Hint "not a class" t] Nothing

convertTypeToKind :: ClassMap -> Type -> Result Kind

convertTypeToKind cMap (FunType t1 FunArr t2 ps) = 
    do k1 <- convertTypeToKind cMap t1
       k2 <- convertTypeToKind cMap t2
       return $ KindAppl k1 k2 ps

convertTypeToKind cMap (BracketType Parens [t] _) = 
    do k <- convertTypeToKind cMap t
       return $ k

convertTypeToKind cMap (MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> Result [] Nothing
	      _ -> do k1 <- convertTypeToClass cMap t1
		      return $ ExtClass k1 v [tokPos t]

convertTypeToKind cMap t = 
    do c <-  convertTypeToClass cMap t
       return $ ExtClass c InVar []

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t s q) = 
    if isSimpleId v then
       do cMap <- getClassMap 
	  let Result ds mc = convertTypeToKind cMap t 
	  case mc of
	       Just c -> anaTypeVarDecl(TypeArg v c s q)
	       Nothing -> anaVarDecl vd
	  appendDiags ds
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ _) = 
		   do (mk, t) <- anaType oldT
		      case mk of 
			      Nothing -> return ()
			      Just k -> checkKinds (posOfId v) k star
		      addOpId v (simpleTypeScheme t) [] VarDefn

-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaBasicItem $ map item l


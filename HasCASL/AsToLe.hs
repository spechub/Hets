
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
import qualified Common.Lib.Map as Map
import Common.Id
import HasCASL.Le
import Common.Lexer 
import Data.Maybe
import Control.Monad
import Control.Monad.State
import HasCASL.OpDecl
import Common.Result
import HasCASL.PrintAs
import HasCASL.TypeAna
import HasCASL.TypeDecl

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

anaBasicSpec :: BasicSpec -> State Env ()
anaBasicSpec (BasicSpec l) = mapM_ anaBasicItem $ map item l

anaBasicItem :: BasicItem -> State Env ()
anaBasicItem (SigItems i) = anaSigItems Loose i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaBasicItem t@(ProgItems _ p) = missingAna t p
anaBasicItem (FreeDatatype l _) = mapM_ (anaDatatype Free Plain) $ map item l
anaBasicItem (GenItems l _) = mapM_ (anaSigItems Generated) $ map item l
anaBasicItem t@(AxiomItems _ _ p) = missingAna t p 

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
              in if null ds then 
                 Result [] (Just $ Intersection [ci] [])
                 else Result [mkDiag Hint "not a class" ci] Nothing

convertTypeToClass cMap (BracketType Parens ts ps) = 
       do cs <- mapM (convertTypeToClass cMap) ts
	  return $ Intersection (concatMap iclass cs) ps

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
			      Just k -> if eqKind Compatible k star
					then  return ()
					else addDiag $
					     mkDiag Error
					("wrong kind '" ++ showPretty k
					 "' of type for variable") v 
		      as <- getAssumps
		      let l = Map.findWithDefault [] v as
			  ts = simpleTypeScheme t in 
			  if ts `elem` l then 
			     addDiag $ mkDiag Warning 
				      "repeated variable '" v
			     else  putAssumps $ Map.insert v (ts:l) as


-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaBasicItem $ map item l


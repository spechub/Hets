
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import ClassDecl
import FiniteMap
import Id
import Le
import Maybe
import Monad
import MonadState
import PrintAs()
import ParseTerm(isSimpleId)
import Result
import TypeAna
import TypeDecl

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

anaBasicSpec :: BasicSpec -> State Env ()
anaBasicSpec (BasicSpec l) = mapM_ anaAnnotedBasicItem l

anaAnnotedBasicItem :: Annoted BasicItem -> State Env ()
anaAnnotedBasicItem i = anaBasicItem $ item i 

anaBasicItem :: BasicItem -> State Env ()
anaBasicItem (SigItems i) = anaSigItems i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaBasicItem t@(ProgItems _ p) = missingAna t p
anaBasicItem t@(FreeDatatype _ p) = missingAna t p 
anaBasicItem t@(GenItems _ p) = missingAna t p
anaBasicItem t@(AxiomItems _ _ p) = missingAna t p 

anaSigItems :: SigItems -> State Env ()
anaSigItems (TypeItems inst l _) = mapM_ (anaAnnotedTypeItem inst) l
anaSigItems l@(OpItems _ p) = missingAna l p 
anaSigItems l@(PredItems _ p) = missingAna l p 

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

anaGenVarDecl :: GenVarDecl -> State Env ()
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeVarDecl t

convertTypeToClass :: ClassMap -> Type -> Result Class
convertTypeToClass cMap (TypeToken t) = 
       if tokStr t == "Type" then Result [] (Just $ universe) else 
	  let ci = simpleIdToId t
	      ds = anaClassId cMap ci
	      in if null ds then 
		 Result [] (Just $ Intersection [ci] [])
		 else Result ds Nothing

convertTypeToClass cMap (BracketType Parens ts ps) = 
       let is = map (convertTypeToClass cMap) ts
	   mis = map maybeResult is
	   ds = concatMap diags is
	   in if all isJust mis then Result ds 
	      (Just $ Intersection (concatMap (iclass . fromJust) mis) ps)
	      else Result ds Nothing

convertTypeToClass _ _ = Result [] Nothing

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t s q) = 
    if isSimpleId v then
       do cMap <- getClassMap 
	  let Result _ mc = convertTypeToClass cMap t 
	      in case mc of
	       Just c -> anaTypeVarDecl(TypeVarDecl v (Kind [] c []) s q)
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ p) = 
		   do t <- anaType oldT
		      as <- getAssumps
		      let l = lookupWithDefaultFM as [] v 
			  ts = SimpleTypeScheme t in 
			  if ts `elem` l then 
			     appendDiags 
				     [Diag Warning 
				      ("repeated variable '" 
				       ++ showId v "'") p ]
			     else  putAssumps $ addToFM as v (ts:l)

anaTypeVarDecl :: TypeVarDecl -> State Env ()
anaTypeVarDecl(TypeVarDecl t k _ _) = 
    do nk <- anaKind k
       addTypeKind t k
       addTypeVar t
-- ------------------------------------------------------------------------------ ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaAnnotedBasicItem l

-- ----------------------------------------------------------------------------
-- TypeItem
-- ----------------------------------------------------------------------------

anaAnnotedTypeItem :: Instance -> Annoted TypeItem -> State Env ()
anaAnnotedTypeItem inst i = anaTypeItem inst $ item i


-- ----------------------------------------------------------------------------
-- addTypeKind
-- ----------------------------------------------------------------------------


{- 
-- add instances later on
	  let ce = classEnv e 
	      mc = lookupFM ce ci 
	    in case mc of 
	       Nothing -> do appendDiags [Error ("undeclared class '"
					     ++ tokStr c ++ "'")
				     $ tokPos c]
			     return star
	       Just info -> do put $ e { classEnv =
				      addToFM ce ci info 
				      { instances = 
					[] :=> (ci `IsIn` TCon (Tycon t k))
					: instances info } }
			       return k
-}


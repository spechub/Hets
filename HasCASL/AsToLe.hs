
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import ClassAna
import ClassDecl
import FiniteMap
import Id
import Le
import Lexer 
import Maybe
import Monad
import MonadState
import OpDecl
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
anaSigItems (OpItems l _) =  mapM_ anaAnnotedOpItem l
anaSigItems l@(PredItems _ p) = missingAna l p 

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
	       Just c -> anaTypeVarDecl(TypeArg v (PlainClass c) s q)
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ _) = 
		   do t <- anaType oldT
		      as <- getAssumps
		      let l = lookupWithDefaultFM as [] v 
			  ts = simpleTypeScheme t in 
			  if ts `elem` l then 
			     addDiag $ mkDiag Warning 
				      "repeated variable '" v
			     else  putAssumps $ addToFM as v (ts:l)

anaTypeVarDecl :: TypeArg -> State Env ()
anaTypeVarDecl(TypeArg t k _ _) = 
    do nk <- anaKind k
       addTypeKind TypeVarDefn t k

-- ----------------------------------------------------------------------------
-- ClassItem
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
-- OpItem
-- ----------------------------------------------------------------------------

anaAnnotedOpItem ::  Annoted OpItem -> State Env ()
anaAnnotedOpItem i = anaOpItem $ item i

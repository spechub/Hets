
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import Id
import Le
import Monad
import MonadState
import FiniteMap
import Result

data LEnv = LEnv { classenv :: ClassEnv
		 , assumps :: Assumps
		 , diags :: [Diagnosis]
		 }

-----------------------------------------------------------------------------
-- FiniteMap stuff
-----------------------------------------------------------------------------

lookUp :: (Ord a, MonadPlus m) => FiniteMap a (m b) -> a -> (m b)
lookUp ce = lookupWithDefaultFM ce mzero

writeMsg e s = put (e {diags = s : diags e})

anaBasicSpec (BasicSpec l) = mapM_ anaAnnotedBasicItem l

anaAnnotedBasicItem i = anaBasicItem $ item i 

anaBasicItem (SigItems i) = anaSigItems i

anaSigItems(TypeItems inst l _) = mapM_ (anaAnnotedTypeItem inst) l

anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem inst (TypeDecl pats kind _) = 
    mapM_ (anaTypePattern inst kind) pats 

anaTypePattern inst kind (TypePatternToken t) = 
    let i = simpleIdToId t
    in 
    do k <- anaPlainKind kind
       let ty = [] :=> TCon (Tycon i k)
	 in do addTypeScheme i (Scheme [] ty)
	       anaKind kind ty
       

anaPlainKind (Kind [] _  _) = return star 
anaKind (Kind [] (As.Universe _) _) _ = return ()
anaKind (Kind [] (As.ClassName ci) _) (qs :=> t) = 
    let i = simpleIdToId ci in
    do e <- get
       let cs = classenv e 
           m = lookupFM cs i 
	 in case m of 
	    Nothing -> writeMsg e (Error ("undeclared class '"
					  ++ showId i "'")
				   $ posOfId i)
	    Just (sc, is) -> put (e {classenv =
				     addToFM cs i (sc, 
						   (qs :=> 
						    (i `IsIn` t))
						   : is)})


-- addTypeScheme :: Id -> Scheme -> State LEnv ()
addTypeScheme i sc = do 
		     e <- get 
		     let as = assumps e 
                         l = lookUp as i in
                       if sc `elem` l then
			  writeMsg e (Warning ("repeated declaration for '" 
					       ++ showId i "'")
				     $ posOfId i)
		       else put (e {assumps = addToFM as i (sc:l)})

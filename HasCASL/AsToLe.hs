
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
    do k <- anaKind kind
       addTypeScheme i (Scheme [] ([] :=> TCon (Tycon i k)))

anaKind (Kind [] (As.Universe _) _) = return star 

-- addTypeScheme :: Id -> Scheme -> State LEnv ()
addTypeScheme i sc = do 
		     e <- get 
		     let as = assumps e 
                         l = lookUp as i in
                       if sc `elem` l then
			  writeMsg e (Warning "repeated declaration" nullPos)
		       else put (e {assumps = addToFM as i (sc:l)})

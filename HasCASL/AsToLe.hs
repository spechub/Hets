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
import Common.GlobalAnnotations
import Common.Lib.State
import Common.Named
import HasCASL.As
import HasCASL.Le
import HasCASL.ClassDecl
import HasCASL.VarDecl
import HasCASL.OpDecl
import HasCASL.TypeDecl
import Data.Maybe

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

anaBasicSpec :: GlobalAnnos -> BasicSpec -> State Env BasicSpec
anaBasicSpec ga (BasicSpec l) = fmap BasicSpec $ 
				mapAnM (anaBasicItem ga) l

anaBasicItem :: GlobalAnnos -> BasicItem -> State Env BasicItem
anaBasicItem ga (SigItems i) = fmap SigItems $ anaSigItems ga Loose i
anaBasicItem ga (ClassItems inst l ps) = 
    do ul <- mapAnM (anaClassItem ga inst) l
       return $ ClassItems inst ul ps
anaBasicItem _ (GenVarItems l ps) = 
    do ul <- mapM anaGenVarDecl l
       return $ GenVarItems (catMaybes ul) ps
anaBasicItem ga (ProgItems l ps) = 
    do ul <- mapAnM (anaProgEq ga) l
       return $ ProgItems ul ps
anaBasicItem _ (FreeDatatype l ps) = 
    do ul <- mapAnM (anaDatatype Free Plain) l
       return $ FreeDatatype ul ps
anaBasicItem ga (GenItems l ps) = 
    do ul <- mapAnM (anaSigItems ga Generated) l
       return $ GenItems ul ps
anaBasicItem ga (AxiomItems decls fs ps) = 
    do tm <- gets typeMap -- save type map
       as <- gets assumps -- save vars
       ds <- mapM anaGenVarDecl decls
       ts <- mapM (anaFormula ga) fs
       putTypeMap tm -- restore 
       putAssumps as -- restore
       let newFs = catMaybes ts
           sens = map ( \ f -> NamedSen (getRLabel f) $ item f) newFs 
       appendSentences sens
       return $ AxiomItems (catMaybes ds) newFs ps

appendSentences :: [Named Term] -> State Env ()
appendSentences fs =
    do e <- get
       put $ e {sentences = sentences e ++ fs}

anaSigItems :: GlobalAnnos -> GenKind -> SigItems -> State Env SigItems
anaSigItems ga gk (TypeItems inst l ps) = 
    do ul <- mapAnM (anaTypeItem ga gk inst) l
       return $ TypeItems inst ul ps
anaSigItems ga _ (OpItems l ps) = 
    do ul <- mapAnM (anaOpItem ga) l
       return $ OpItems ul ps

-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaClassItem :: GlobalAnnos -> Instance -> ClassItem 
		    -> State Env ClassItem
anaClassItem ga _ (ClassItem d l ps) = 
    do cd <- anaClassDecls d 
       ul <- mapAnM (anaBasicItem ga) l
       return $ ClassItem cd ul ps

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
import HasCASL.MixAna
import Data.Maybe

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

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
    do e <- get
       put $ e {sentences = sentences e ++ fs}

anaSigItems :: GlobalAnnos -> GenKind -> SigItems -> State Env ()
anaSigItems _ gk (TypeItems inst l _) = 
    mapM_ (anaTypeItem gk inst) $ map item l
anaSigItems ga _ (OpItems l _) =  mapM_ (anaOpItem ga) $ map item l

-- ----------------------------------------------------------------------------
-- ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: GlobalAnnos -> Instance -> Annoted ClassItem 
		    -> State Env ()
anaAnnotedClassItem ga _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ (anaBasicItem ga) $ map item l


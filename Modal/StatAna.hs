{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   static analysis of modal logic parts
-}

module Modal.StatAna where

import Modal.AS_Modal
import Modal.Print_AS
import Modal.ModalSign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.MapSentence

import Common.AS_Annotation
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Common.Id
import Common.Result

minExpForm :: Min M_FORMULA ModalSign
minExpForm ga s form = 
    let newGa = addAssocs ga s
	ops = formulaIds s
        preds = allPredIds s
	res = resolveFormula newGa ops preds
        minMod md ps = case md of
	          Simple_mod i -> minMod (Term_mod (Mixfix_token i)) ps
		  Term_mod t -> let
		    r = do 
		      t1 <- resolveMixfix newGa (allOpIds s) preds False t
		      ts <- minExpTerm minExpForm ga s t1
		      t2 <- is_unambiguous t ts ps
		      let srt = term_sort t2
			  trm = Term_mod t2
		      if Set.member srt $ termModies $ extendedInfo s 
			 then return trm
		         else Result [mkDiag Error 
			      ("unknown term modality sort '"
			       ++ showId srt "' for term") t ]
			      $ Just trm
		    in case t of
		       Mixfix_token tm -> 
			   if Set.member tm $ modies $ extendedInfo s 
			      then return $ Simple_mod tm
			      else case maybeResult r of
			          Nothing -> Result 
				      [mkDiag Error "unknown modality" tm]
				      $ Just $ Simple_mod tm
				  _ -> r
		       _ -> r
    in case form of
        Box m f ps -> 
	    do nm <- minMod m ps
               f1 <- res f
	       f2 <- minExpFORMULA minExpForm ga s f1
	       return $ Box nm f2 ps
	Diamond m f ps -> 
	    do nm <- minMod m ps
               f1 <- res f
	       f2 <- minExpFORMULA minExpForm ga s f1
	       return $ Diamond nm f2 ps

ana_M_SIG_ITEM :: Ana M_SIG_ITEM M_FORMULA ModalSign
ana_M_SIG_ITEM ga mi = 
    case mi of 
    Rigid_op_items r al ps -> 
	do ul <- mapM (ana_OP_ITEM ga) al 
	   case r of
               Rigid -> mapM_ ( \ aoi -> case item aoi of 
		   Op_decl ops ty _ _ -> 
		       mapM_ (updateExtInfo . addRigidOp (toOpType ty)) ops
		   Op_defn i par _ _ -> 
		       updateExtInfo $ addRigidOp (toOpType $ headToType par) 
				i ) ul
               _ -> return ()
	   return $ Rigid_op_items r ul ps
    Rigid_pred_items r al ps -> 
	do ul <- mapM (ana_PRED_ITEM ga) al 
	   case r of
               Rigid -> mapM_ ( \ aoi -> case item aoi of 
		   Pred_decl ops ty _ -> 
		       mapM_ (updateExtInfo . addRigidPred (toPredType ty)) ops
	           Pred_defn i (Pred_head args _) _ _ -> 
		       updateExtInfo $ addRigidPred 
			        (PredType $ sortsOfArgs args) i ) ul
               _ -> return ()
	   return $ Rigid_pred_items r ul ps

addRigidOp :: OpType -> Id -> ModalSign -> Result ModalSign
addRigidOp ty i m = return
       m { rigidOps = addTo i ty { opKind = Partial } $ rigidOps m }

addRigidPred :: PredType -> Id -> ModalSign -> Result ModalSign
addRigidPred ty i m = return
       m { rigidPreds = addTo i ty $ rigidPreds m }

ana_M_BASIC_ITEM :: Ana M_BASIC_ITEM M_FORMULA ModalSign
ana_M_BASIC_ITEM _ bi = do
    e <- get
    case bi of
        Simple_mod_decl al _ -> mapM_ ((updateExtInfo . addModId) . item) al
	Term_mod_decl al _ -> mapM_ ((updateExtInfo . addModSort e) . item) al
    return bi

addModId :: SIMPLE_ID -> ModalSign -> Result ModalSign
addModId i m = 
    let ms = modies m in 
    if Set.member i ms then 
       Result [mkDiag Hint "repeated modality" i] $ Just m
       else return m { modies = Set.insert i ms }

addModSort :: Sign M_FORMULA ModalSign -> SORT -> ModalSign -> Result ModalSign
addModSort e i m = 
    let ms = termModies m
        ds = hasSort e i 
    in if Set.member i ms || not (null ds) then 
       Result (mkDiag Hint "repeated term modality" i : ds) $ Just m
       else return m { termModies = Set.insert i ms }

map_M_FORMULA :: MapSen M_FORMULA ModalSign ()
map_M_FORMULA mor frm =
    let mapMod m = case m of 
		   Simple_mod _ -> return m
		   Term_mod t -> do newT <- mapTerm map_M_FORMULA mor t
				    return $ Term_mod newT
	in case frm of
	   Box m f ps -> do 
	       newF <- mapSen map_M_FORMULA mor f
	       newM <- mapMod m 
	       return $ Box newM newF ps 
	   Diamond m f ps -> do 
	       newF <- mapSen map_M_FORMULA mor f
	       newM <- mapMod m 
	       return $ Diamond newM newF ps 

{- |
Module      :  ./Hybrid/StatAna.hs
Copyright   :  (c) Christian Maeder, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of hybrid logic parts
-}

module Hybrid.StatAna (basicHybridAnalysis, minExpForm) where

import Hybrid.AS_Hybrid
import Hybrid.Print_AS ()
import Hybrid.HybridSign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Keywords
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet

import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set
import Data.List as List

instance TermExtension H_FORMULA where
        freeVarsOfExt sign (BoxOrDiamond _ _ f _) = freeVars sign f
        freeVarsOfExt sign (At _ f _ ) = freeVars sign f
        freeVarsOfExt sign (Univ _ f _) = freeVars sign f
        freeVarsOfExt sign (Exist _ f _) = freeVars sign f
        freeVarsOfExt _ (Here _ _ ) = Set.empty

basicHybridAnalysis
  :: (BASIC_SPEC H_BASIC_ITEM H_SIG_ITEM H_FORMULA,
      Sign H_FORMULA HybridSign, GlobalAnnos)
  -> Result (BASIC_SPEC H_BASIC_ITEM H_SIG_ITEM H_FORMULA,
             ExtSign (Sign H_FORMULA HybridSign) Symbol,
             [Named (FORMULA H_FORMULA)])
basicHybridAnalysis =
       basicAnalysis minExpForm ana_H_BASIC_ITEM ana_H_SIG_ITEM ana_Mix

ana_Mix :: Mix H_BASIC_ITEM H_SIG_ITEM H_FORMULA HybridSign
ana_Mix = emptyMix
    { getSigIds = ids_H_SIG_ITEM
    , putParen = mapH_FORMULA
    , mixResolve = resolveH_FORMULA
    }

-- rigid ops will also be part of the CASL signature
ids_H_SIG_ITEM :: H_SIG_ITEM -> IdSets
ids_H_SIG_ITEM si = let e = Set.empty in case si of
    Rigid_op_items _ al _ ->
        (unite2 $ map (ids_OP_ITEM . item) al, e)
    Rigid_pred_items _ al _ ->
        ((e, e), Set.unions $ map (ids_PRED_ITEM . item) al)

mapMODALITY :: MODALITY -> MODALITY
mapMODALITY m = case m of
    Term_mod t -> Term_mod $ mapTerm mapH_FORMULA t
    _ -> m

mapH_FORMULA :: H_FORMULA -> H_FORMULA
mapH_FORMULA (BoxOrDiamond b m f ps) =
    BoxOrDiamond b (mapMODALITY m) (mapFormula mapH_FORMULA f) ps
mapH_FORMULA (At n f ps) = At n (mapFormula mapH_FORMULA f) ps
mapH_FORMULA (Univ n f ps) = Univ n (mapFormula mapH_FORMULA f) ps
mapH_FORMULA (Exist n f ps) = Exist n (mapFormula mapH_FORMULA f) ps
mapH_FORMULA (Here n ps) = Here n ps

resolveMODALITY :: MixResolve MODALITY
resolveMODALITY ga ids m = case m of
    Term_mod t -> fmap Term_mod $ resolveMixTrm mapH_FORMULA
                  resolveH_FORMULA ga ids t
    _ -> return m

resolveH_FORMULA :: MixResolve H_FORMULA
resolveH_FORMULA ga ids cf = case cf of
   BoxOrDiamond b m f ps -> do
       nm <- resolveMODALITY ga ids m
       nf <- resolveMixFrm mapH_FORMULA resolveH_FORMULA ga ids f
       return (BoxOrDiamond b nm nf ps)
   At n f ps -> do
       nf <- resolveMixFrm mapH_FORMULA resolveH_FORMULA ga ids f
       return (At n nf ps)
   Univ n f ps -> do
       nf <- resolveMixFrm mapH_FORMULA resolveH_FORMULA ga ids f
       return (Univ n nf ps)
   Exist n f ps -> do
       nf <- resolveMixFrm mapH_FORMULA resolveH_FORMULA ga ids f
       return (Exist n nf ps)
   Here n ps -> return (Here n ps)

minExpForm :: Min H_FORMULA HybridSign
minExpForm s form =
    let minMod md ps = case md of
                  Simple_mod i -> minMod (Term_mod (Mixfix_token i)) ps
                  Term_mod t -> let
                    r = do
                      t2 <- oneExpTerm minExpForm s t
                      let srt = sortOfTerm t2
                          trm = Term_mod t2
                          supers = supersortsOf srt s
                      if Set.null $ Set.intersection
                        (Set.insert srt supers)
                         $ Set.fromList $ Map.keys $ termModies $ extendedInfo s
                         then Result [mkDiag Error
                              ("unknown term modality sort '"
                               ++ showId srt "' for term") t ]
                              $ Just trm
                         else return trm
                    in case t of
                       Mixfix_token tm ->
                           if Map.member tm (modies $ extendedInfo s)
                              || tokStr tm == emptyS
                              then return $ Simple_mod tm
                              else Result
                                      [mkDiag Error "unknown modality" tm]
                                      $ Just $ Simple_mod tm
                       Application (Op_name (Id [tm] [] _)) [] _ ->
                           if Map.member tm (modies $ extendedInfo s)
                           then return $ Simple_mod tm
                           else r
                       _ -> r
        minNom (Simple_nom n) = if Map.member n (nomies $ extendedInfo s)
                                then return (Simple_nom n)
                                else Result [mkDiag Error "unknown nominal" n]
                                            $ Just (Simple_nom n)
        colNom (Simple_nom n)
         | Map.member n (nomies $ extendedInfo s) = Result
            [mkDiag Error "collision on nominals" n] $ Just (Simple_nom n)
         | wPrefix n = Result
            [mkDiag Error "\"world\" prefixes are reserved" n] Nothing
         | otherwise = return (Simple_nom n)
        addUniv (Simple_nom n) = addNomId [] n
        addExist (Simple_nom n ) = addNomId [] n
    in case form of
        BoxOrDiamond b m f ps ->
            do nm <- minMod m ps
               nf <- minExpFORMULA minExpForm s f
               return (BoxOrDiamond b nm nf ps)
        At n f ps ->
            do nn <- minNom n
               nf <- minExpFORMULA minExpForm s f
               return (At nn nf ps)
        Univ n f ps ->
            do nn <- colNom n
               {- add the binder in the sign (for this formula only)
               so it can be used a normal nominal -}
               bs <- addUniv nn (extendedInfo s)
               nf <- minExpFORMULA minExpForm (s {extendedInfo = bs}) f
               return (Univ nn nf ps)
        Exist n f ps ->
            do nn <- colNom n
               {- add the binder in the sign (for this formula only)
               so it can be used a normal nominal -}
               bs <- addExist nn (extendedInfo s)
               nf <- minExpFORMULA minExpForm (s {extendedInfo = bs}) f
               return (Exist nn nf ps)

        Here n ps ->
            do nn <- minNom n
               return (Here nn ps)

ana_H_SIG_ITEM :: Ana H_SIG_ITEM H_BASIC_ITEM H_SIG_ITEM H_FORMULA HybridSign
ana_H_SIG_ITEM mix mi =
    case mi of
    Rigid_op_items r al ps ->
        do ul <- mapM (ana_OP_ITEM minExpForm mix) al
           case r of
               Rigid -> mapM_ (\ aoi -> case item aoi of
                   Op_decl ops ty _ _ ->
                       mapM_ (updateExtInfo . addRigidOp (toOpType ty)) ops
                   Op_defn i par _ _ -> maybe (return ())
                       (\ ty -> updateExtInfo $ addRigidOp (toOpType ty) i)
                       $ headToType par) ul
               _ -> return ()
           return $ Rigid_op_items r ul ps
    Rigid_pred_items r al ps ->
        do ul <- mapM (ana_PRED_ITEM minExpForm mix) al
           case r of
               Rigid -> mapM_ (\ aoi -> case item aoi of
                   Pred_decl ops ty _ ->
                       mapM_ (updateExtInfo . addRigidPred (toPredType ty)) ops
                   Pred_defn i (Pred_head args _) _ _ ->
                       updateExtInfo $ addRigidPred
                                (PredType $ sortsOfArgs args) i ) ul
               _ -> return ()
           return $ Rigid_pred_items r ul ps

addRigidOp :: OpType -> Id -> HybridSign -> Result HybridSign
addRigidOp ty i m = return
       m { rigidOps = addOpTo i ty $ rigidOps m }

addRigidPred :: PredType -> Id -> HybridSign -> Result HybridSign
addRigidPred ty i m = return
       m { rigidPreds = MapSet.insert i ty $ rigidPreds m }

ana_H_BASIC_ITEM
    :: Ana H_BASIC_ITEM H_BASIC_ITEM H_SIG_ITEM H_FORMULA HybridSign
ana_H_BASIC_ITEM mix bi =
 let anaHlp fs = do
      newFs <- mapAnM (ana_FORMULA mix) fs
      resFs <- mapAnM (return . fst) newFs
      anaFs <- mapAnM (return . snd) newFs
      return (resFs, anaFs)
 in case bi of
        Simple_mod_decl al fs ps -> do
            mapM_ ((updateExtInfo . preAddModId) . item) al
            (resFs, anaFs) <- anaHlp fs
            mapM_ ((updateExtInfo . addModId anaFs) . item) al
            return $ Simple_mod_decl al resFs ps
        Term_mod_decl al fs ps -> do
            e <- get
            mapM_ ((updateExtInfo . preAddModSort e) . item) al
            (resFs, anaFs) <- anaHlp fs
            mapM_ ((updateExtInfo . addModSort anaFs) . item) al
            return $ Term_mod_decl al resFs ps
        Simple_nom_decl ids fs ps -> do
           mapM_ ((updateExtInfo . preAddNomId) . item) ids
           (resFs, anaFs) <- anaHlp fs
           mapM_ ((updateExtInfo . addNomId anaFs) . item) ids
           return $ Simple_nom_decl ids resFs ps

preAddNomId :: SIMPLE_ID -> HybridSign -> Result HybridSign
preAddNomId i hs =
    let ns = nomies hs in
    if Map.member i ns then
        Result [mkDiag Hint "repeated nominal" i] $ Just hs
        else if wPrefix i
                then Result [mkDiag Error "\"world\" prefixes are reserved" i]
                      Nothing
                else return hs { nomies = Map.insert i [] ns }

preAddModId :: SIMPLE_ID -> HybridSign -> Result HybridSign
preAddModId i m =
    let ms = modies m in
    if Map.member i ms then
       Result [mkDiag Hint "repeated modality" i] $ Just m
       else return m { modies = Map.insert i [] ms }

addNomId :: [AnHybFORM] -> SIMPLE_ID -> HybridSign -> Result HybridSign
addNomId frms i s =
        return s { nomies = Map.insertWith List.union i frms $ nomies s}

addModId :: [AnHybFORM] -> SIMPLE_ID -> HybridSign -> Result HybridSign
addModId frms i m = return m
  { modies = Map.insertWith List.union i frms $ modies m }

preAddModSort :: Sign H_FORMULA HybridSign -> SORT -> HybridSign
              -> Result HybridSign
preAddModSort e i m =
    let ms = termModies m
        ds = hasSort e i
    in if Map.member i ms || not (null ds) then
       Result (mkDiag Hint "repeated term modality" i : ds) $ Just m
       else return m { termModies = Map.insert i [] ms }

addModSort :: [AnHybFORM] -> SORT -> HybridSign -> Result HybridSign
addModSort frms i m = return m
  { termModies = Map.insertWith List.union i frms $ termModies m }

ana_FORMULA :: Mix H_BASIC_ITEM H_SIG_ITEM H_FORMULA HybridSign
            -> FORMULA H_FORMULA -> State (Sign H_FORMULA HybridSign)
               (FORMULA H_FORMULA, FORMULA H_FORMULA)
ana_FORMULA mix f = do
           let ps = map (mkId . (: [])) $ Set.toList $ getFormPredToks f
           pm <- gets predMap
           mapM_ (addPred (emptyAnno ()) $ PredType []) ps
           newGa <- gets globAnnos
           let Result es m = resolveFormula mapH_FORMULA
                             resolveH_FORMULA newGa (mixRules mix) f
           addDiags es
           e <- get
           phi <- case m of
               Nothing -> return (f, f)
               Just r -> do
                   n <- resultToState (minExpFORMULA minExpForm e) r
                   return (r, n)
           e2 <- get
           put e2 {predMap = pm}
           return phi

getFormPredToks :: FORMULA H_FORMULA -> Set.Set Token
getFormPredToks frm = case frm of
    Quantification _ _ f _ -> getFormPredToks f
    Junction _ fs _ -> Set.unions $ map getFormPredToks fs
    Relation f1 _ f2 _ ->
        Set.union (getFormPredToks f1) $ getFormPredToks f2
    Negation f _ -> getFormPredToks f
    Mixfix_formula (Mixfix_token t) -> Set.singleton t
    Mixfix_formula t -> getTermPredToks t
    ExtFORMULA (BoxOrDiamond _ _ f _) -> getFormPredToks f
    ExtFORMULA (At _ f _ ) -> getFormPredToks f
    ExtFORMULA (Univ _ f _ ) -> getFormPredToks f
    ExtFORMULA (Exist _ f _ ) -> getFormPredToks f
    Predication _ ts _ -> Set.unions $ map getTermPredToks ts
    Definedness t _ -> getTermPredToks t
    Membership t _ _ -> getTermPredToks t
    _ -> Set.empty

getTermPredToks :: TERM H_FORMULA -> Set.Set Token
getTermPredToks trm = case trm of
    Application _ ts _ -> Set.unions $ map getTermPredToks ts
    Sorted_term t _ _ -> getTermPredToks t
    Cast t _ _ -> getTermPredToks t
    Conditional t1 f t2 _ -> Set.union (getTermPredToks t1) $
        Set.union (getFormPredToks f) $ getTermPredToks t2
    Mixfix_term ts -> Set.unions $ map getTermPredToks ts
    Mixfix_parenthesized ts _ -> Set.unions $ map getTermPredToks ts
    Mixfix_bracketed ts _ -> Set.unions $ map getTermPredToks ts
    Mixfix_braced ts _ -> Set.unions $ map getTermPredToks ts
    _ -> Set.empty


wPrefix :: Token -> Bool
wPrefix = isPrefixOf "world" . tokStr

{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/Modal2CASL.hs
Copyright   :  (c) Klaus Luettich, Uni Bremen 2004, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The possible world encoding comorphism from ModalCASL to CASL.

   We use the Relational Translation by adding one extra parameter of
   type world to each predicate.

-}

module Comorphisms.Modal2CASL (Modal2CASL (..)) where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.World

-- ModalCASL
import Modal.Logic_Modal
import Modal.AS_Modal
import Modal.ModalSign
import Modal.Utils

-- generated function
import Modal.ModalSystems

import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import Data.Maybe

import GHC.Generics (Generic)
import Data.Hashable

-- | The identity of the comorphism
data Modal2CASL = Modal2CASL deriving (Show)

instance Language Modal2CASL -- default definition is okay

instance Comorphism Modal2CASL
               Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign
               ModalMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic Modal2CASL = Modal
    sourceSublogic Modal2CASL = ()
    targetLogic Modal2CASL = CASL
    mapSublogic Modal2CASL _ = Just SL.caslTop
      { sub_features = LocFilSub
      , cons_features = NoSortGen
      } -- to support going to SPASS
    map_theory (Modal2CASL) (sig, sens) = case transSig sig of
      mme -> return (caslSign mme, relFormulas mme
                     ++ map (mapNamed $ transSen sig) sens)
    map_morphism Modal2CASL = return . mapMor
    map_sentence Modal2CASL sig = return . transSen sig
    map_symbol Modal2CASL _ = Set.singleton . mapSym
    has_model_expansion Modal2CASL = True
    is_weakly_amalgamable Modal2CASL = True

data ModName = SimpleM SIMPLE_ID
             | SortM SORT
               deriving (Show, Ord, Eq, Generic)

instance Hashable ModName

-- | relations on possible worlds
type ModalityRelMap = Map.HashMap ModName PRED_NAME

data ModMapEnv = MME
    { caslSign :: CASLSign
    , worldSort :: SORT
    , modalityRelMap :: ModalityRelMap
    , flexiOps :: OpMap
    , flexiPreds :: PredMap
    , relFormulas :: [Named CASLFORMULA] }

transSig :: MSign -> ModMapEnv
transSig sign =
   let extInf = extendedInfo sign
       flexibleOps = flexOps extInf
       flexiblePreds = flexPreds extInf
       fws = world
       flexOps' = addWorldOp fws addPlace flexibleOps
       flexPreds' = MapSet.fromMap . addWorldRels True relsTermMod
                    . addWorldRels False relsMod . MapSet.toMap
                    $ addWorldPred fws addPlace flexiblePreds
       rigOps' = diffOpMapSet (opMap sign) flexibleOps
       rigPreds' = diffMapSet (predMap sign) flexiblePreds
       relations = Map.union relsMod relsTermMod
       genRels f = Map.foldrWithKey (\ me _ nm -> f me nm) Map.empty
       relSymbS = relName False . simpleIdToId
       relSymbT = relName True
       genModFrms f = Map.foldrWithKey f []
       modiesInf = modies extInf
       trmMods = termModies extInf
       relsMod = genRels (\ me nm -> Map.insert (SimpleM me) (relSymbS me) nm)
                         modiesInf
       relsTermMod = genRels (\ me nm ->
                                  Map.insert (SortM me) (relSymbT me) nm)
                             trmMods
       relModFrms = genModFrms (\ me frms trFrms -> trFrms ++
                                         transSchemaMFormulas partMME
                                                  fws (relSymbS me) frms)
                               modiesInf
       relTermModFrms = genModFrms (\ me frms trFrms -> trFrms ++
                                         transSchemaMFormulas partMME
                                                  fws (relSymbT me) frms)
                               trmMods
       addWorldRels isTermMod rels mp =
              let argSorts rs = if isTermMod
                             then [getModTermSort rs, fws, fws]
                             else [fws, fws] in
               Map.foldr (\ rs nm -> Map.insert rs
                                              (Set.singleton $
                                                    PredType $ argSorts rs)
                                              nm)
                        mp rels
       partMME = MME {caslSign =
            (emptySign ())
               { sortRel = Rel.insertKey fws $ sortRel sign
               , opMap = addOpMapSet flexOps' rigOps'
               , assocOps = diffOpMapSet (assocOps sign) flexibleOps
               , predMap = addMapSet flexPreds' rigPreds'},
         worldSort = fws,
         modalityRelMap = relations,
         flexiOps = flexibleOps,
         flexiPreds = flexiblePreds,
         relFormulas = []}
      in partMME { relFormulas = relModFrms ++ relTermModFrms}

mapMor :: ModalMor -> CASLMor
mapMor m = (embedMorphism ()
    (caslSign $ transSig $ msource m)
    $ caslSign $ transSig $ mtarget m)
  { sort_map = sort_map m
  , op_map = op_map m
  , pred_map = pred_map m }

mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once modal symbols are added

transSchemaMFormulas :: ModMapEnv -> SORT -> PRED_NAME
                     -> [AnModFORM] -> [Named CASLFORMULA]
transSchemaMFormulas mapEnv fws relSymb =
    mapMaybe (transSchemaMFormula (mapTERM mapEnv) fws relSymb worldVars)

transSen :: MSign -> ModalFORMULA -> CASLFORMULA
transSen msig = mapSenTop (transSig msig)

mapSenTop :: ModMapEnv -> ModalFORMULA -> CASLFORMULA
mapSenTop mapEnv@(MME {worldSort = fws}) f =
    case f of
    Quantification q@Universal vs frm ps ->
        Quantification q (qwv : vs) (mapSen mapEnv wvs frm) ps
    f1 -> mkForall [qwv] (mapSen mapEnv wvs f1)
    where qwv = mkVarDecl v1 fws
          wvs@(v1 : _) = worldVars


-- head [VAR] is always the current world variable (for predication)
mapSen :: ModMapEnv -> [VAR] -> ModalFORMULA -> CASLFORMULA
mapSen mapEnv@(MME {worldSort = fws, flexiPreds = fPreds}) vars
       f = case f of
           Quantification q vs frm ps ->
                  Quantification q vs (mapSen mapEnv vars frm) ps
           Junction j fs ps ->
               Junction j (map (mapSen mapEnv vars) fs) ps
           Relation f1 c f2 ps ->
               Relation (mapSen mapEnv vars f1) c (mapSen mapEnv vars f2) ps
           Negation frm ps -> Negation (mapSen mapEnv vars frm) ps
           Atom b ps -> Atom b ps
           Equation t1 e t2 ps -> Equation
               (mapTERM mapEnv vars t1) e (mapTERM mapEnv vars t2) ps
           Predication pn as qs ->
               let as' = map (mapTERM mapEnv vars) as
                   fwsTerm = mkVarTerm (head vars) fws
                   (pn', as'') =
                       case pn of
                       Pred_name _ -> error "Modal2CASL: untyped predication"
                       Qual_pred_name prn pType@(Pred_type sorts pps) ps ->
                         let addTup = (Qual_pred_name (addPlace prn)
                                             (Pred_type (fws : sorts) pps) ps,
                                       fwsTerm : as')
                             defTup = (pn, as') in
                                 if Set.member (toPredType pType)
                                     $ MapSet.lookup prn fPreds
                                     then addTup
                                     else defTup
               in Predication pn' as'' qs
           Definedness t ps -> Definedness (mapTERM mapEnv vars t) ps
           Membership t ty ps -> Membership (mapTERM mapEnv vars t) ty ps
           Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
           ExtFORMULA mf -> mapMSen mapEnv vars mf
           _ -> error "Modal2CASL.transSen->mapSen"

mapMSen :: ModMapEnv -> [VAR] -> M_FORMULA -> CASLFORMULA
mapMSen mapEnv@(MME {worldSort = fws, modalityRelMap = pwRelMap}) vars f
   = let w1 : w2 : tl = vars
         getRel mo =
              Map.findWithDefault
                    (error ("Modal2CASL: Undefined modality " ++ show mo))
                    (modalityToModName mo)
         vw1 = mkVarDecl w1 fws
         vw2 = mkVarDecl w2 fws
         mkPredType ts = Pred_type ts nullRange
         joinPreds b t1 t2 = if b then mkImpl t1 t2 else conjunct [t1, t2]
     in
     case f of
     BoxOrDiamond b moda f1 _ ->
       let rel = getRel moda pwRelMap
       in (if b then mkForall else mkExist) [vw2] $ joinPreds b
       (case moda of
        Simple_mod _ -> mkPredication
            (mkQualPred rel $ mkPredType [fws, fws])
            [toQualVar vw1, toQualVar vw2]
        Term_mod t -> mkPredication
            (mkQualPred rel $ mkPredType [getModTermSort rel, fws, fws])
            [mapTERM mapEnv (w1 : tl) t, toQualVar vw1, toQualVar vw2]
       ) $ mapSen mapEnv (w2 : tl) f1

-- head [VAR] is always the current world variable (for Application)
mapTERM :: ModMapEnv -> [VAR] -> TERM M_FORMULA -> TERM ()
mapTERM mapEnv@(MME {worldSort = fws, flexiOps = fOps}) vars t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs ->
        let as' = map (mapTERM mapEnv vars) as
            fwsTerm = mkVarTerm (head vars) fws
            addFws (Op_type k sorts res pps) =
                Op_type k (fws : sorts) res pps
            (opsym', as'') =
                case opsym of
                Op_name _ -> error "Modal2CASL: untyped prdication"
                Qual_op_name on opType ps ->
                    let addTup = (Qual_op_name (addPlace on)
                                               (addFws opType) ps,
                                  fwsTerm : as')
                        defTup = (opsym, as') in
                            if Set.member (toOpType opType)
                                $ MapSet.lookup on fOps
                                then addTup
                                else defTup
        in Application opsym' as'' qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM mapEnv vars trm) ty ps
    Cast trm ty ps -> Cast (mapTERM mapEnv vars trm) ty ps
    Conditional t1 f t2 ps ->
       Conditional (mapTERM mapEnv vars t1)
                   (mapSen mapEnv vars f)
                   (mapTERM mapEnv vars t2) ps
    _ -> error "Modal2CASL.mapTERM"

modalityToModName :: MODALITY -> ModName
modalityToModName (Simple_mod sid) = SimpleM sid
modalityToModName (Term_mod t) =
    case optTermSort t of
    Just srt -> SortM srt
    Nothing -> error ("Modal2CASL: modalityToModName: Wrong term: " ++ show t)

-- List of variables for worlds
worldVars :: [SIMPLE_ID]
worldVars = map (genNumVar "w") [1 ..]

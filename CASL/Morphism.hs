{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CASL/Morphism.hs
Description :  Symbols and signature morphisms for the CASL logic
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC+FD)

Symbols and signature morphisms for the CASL logic
-}

module CASL.Morphism
  ( SymbolSet
  , SymbolMap
  , RawSymbol (..)
  , Morphism (..)
  , idMor
  , legalMor
  , DefMorExt (..)
  , emptyMorExt
  , MorphismExtension (..)
  , retExtMap
  , CASLMor
  , isInclusionMorphism
  , isSortInjective
  , isInjective
  , Sort_map
  , Pred_map
  , Op_map
  , embedMorphism
  , mapCASLMor
  , sigInclusion
  , composeM
  , plainMorphismUnion
  , morphismUnion
  , morphismUnionM
  , idOrInclMorphism
  , morphismToSymbMap
  , symsetOf
  , symOf
  , sigSymsOf
  , addSigM
  , idToRaw
  , typedSymbKindToRaw
  , symbolToRaw
  , insertRsys
  , mapSort
  , mapOpSym
  , mapPredSym
  , mapOpType
  , mapPredType
  , matches
  , compatibleOpTypes
  , imageOfMorphism
  , RawSymbolMap
  , InducedSign
  , inducedSignAux
  , rawSymName
  , inducedOpMap
  , inducedPredMap
  , statSymbMapItems
  , statSymbItems
  ) where

import CASL.Sign
import CASL.AS_Basic_CASL

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils (composeMap)

import Control.Monad
import qualified Control.Monad.Fail as Fail

type SymbolSet = Set.Set Symbol
type SymbolMap = Map.Map Symbol Symbol

data RawSymbol = ASymbol Symbol | AKindedSymb SYMB_KIND Id
                 deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange RawSymbol where
    getRange rs = case rs of
        ASymbol s -> getRange s
        AKindedSymb _ i -> getRange i

type RawSymbolMap = Map.Map RawSymbol RawSymbol

type Sort_map = Map.Map SORT SORT
-- always use the partial profile as key!
type Op_map = Map.Map (Id, OpType) (Id, OpKind)
type Pred_map = Map.Map (Id, PredType) Id

data Morphism f e m = Morphism
  { msource :: Sign f e
  , mtarget :: Sign f e
  , sort_map :: Sort_map
  , op_map :: Op_map
  , pred_map :: Pred_map
  , extended_map :: m
  } deriving (Show, Eq, Ord, Typeable, Data)

data DefMorExt e = DefMorExt e deriving (Typeable, Data)

instance Show (DefMorExt e) where
  show = const ""

instance Ord (DefMorExt e) where
  compare _ = const EQ

instance Eq (DefMorExt e) where
  (==) e = (== EQ) . compare e

emptyMorExt :: DefMorExt e
emptyMorExt = DefMorExt $ error "emptyMorExt"

instance Pretty (DefMorExt e) where
  pretty _ = empty

class (Pretty e, Pretty m) => MorphismExtension e m | m -> e where
   ideMorphismExtension :: e -> m
   composeMorphismExtension :: Morphism f e m -> Morphism f e m -> Result m
   inverseMorphismExtension :: Morphism f e m -> Result m
   inverseMorphismExtension = return . extended_map
   isInclusionMorphismExtension :: m -> Bool
   prettyMorphismExtension :: Morphism f e m -> Doc
   prettyMorphismExtension = pretty . extended_map
   legalMorphismExtension :: Morphism f e m -> Result ()
   legalMorphismExtension _ = return ()

instance MorphismExtension () () where
   ideMorphismExtension _ = ()
   composeMorphismExtension _ = return . extended_map
   isInclusionMorphismExtension _ = True

instance Pretty e => MorphismExtension e (DefMorExt e) where
   ideMorphismExtension _ = emptyMorExt
   composeMorphismExtension _ = return . extended_map
   isInclusionMorphismExtension _ = True

type CASLMor = Morphism () () ()

isInclusionMorphism :: (m -> Bool) -> Morphism f e m -> Bool
isInclusionMorphism f m = f (extended_map m) && Map.null (sort_map m)
  && Map.null (pred_map m) && isInclOpMap (op_map m)

mapSort :: Sort_map -> SORT -> SORT
mapSort sorts s = Map.findWithDefault s s sorts

mapOpType :: Sort_map -> OpType -> OpType
mapOpType sorts t = if Map.null sorts then t else
  t { opArgs = map (mapSort sorts) $ opArgs t
    , opRes = mapSort sorts $ opRes t }

makeTotal :: OpKind -> OpType -> OpType
makeTotal fk t = case fk of
  Total -> mkTotal t
  _ -> t

mapOpSym :: Sort_map -> Op_map -> (Id, OpType) -> (Id, OpType)
mapOpSym sMap oMap (i, ot) = let mot = mapOpType sMap ot in
  case Map.lookup (i, mkPartial ot) oMap of
    Nothing -> (i, mot)
    Just (j, k) -> (j, makeTotal k mot)

-- | Check if two OpTypes are equal modulo totality or partiality
compatibleOpTypes :: OpType -> OpType -> Bool
compatibleOpTypes ot1 ot2 = opSorts ot1 == opSorts ot2

mapPredType :: Sort_map -> PredType -> PredType
mapPredType sorts t = if Map.null sorts then t else
  t { predArgs = map (mapSort sorts) $ predArgs t }

mapPredSym :: Sort_map -> Pred_map -> (Id, PredType) -> (Id, PredType)
mapPredSym sMap oMap (i, pt) =
    (Map.findWithDefault i (i, pt) oMap, mapPredType sMap pt)

embedMorphism :: m -> Sign f e -> Sign f e -> Morphism f e m
embedMorphism extEm a b = Morphism
  { msource = a
  , mtarget = b
  , sort_map = Map.empty
  , op_map = Map.empty
  , pred_map = Map.empty
  , extended_map = extEm }

-- | given empty extensions convert a morphism
mapCASLMor :: e -> m -> Morphism f1 e1 m1 -> Morphism f e m
mapCASLMor e me m =
  (embedMorphism me (embedSign e $ msource m) $ embedSign e $ mtarget m)
  { sort_map = sort_map m
  , op_map = op_map m
  , pred_map = pred_map m }

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw = ASymbol

idToRaw :: Id -> RawSymbol
idToRaw = AKindedSymb Implicit

rawSymName :: RawSymbol -> Id
rawSymName rs = case rs of
  ASymbol sym -> symName sym
  AKindedSymb _ i -> i

sortSyms :: Sign f e -> SymbolSet
sortSyms = Set.map idToSortSymbol . sortSet

opSyms :: Sign f e -> [Symbol]
opSyms = map (uncurry idToOpSymbol) . mapSetToList . opMap

predSyms :: Sign f e -> [Symbol]
predSyms = map (uncurry idToPredSymbol) . mapSetToList . predMap

{- | returns the symbol sets of the signature in the correct dependency order
, i.e., sorts first, then ops and predicates. Result list is of length two. -}
symOf :: Sign f e -> [SymbolSet]
symOf s = [ sortSyms s, Set.fromList $ predSyms s ++ opSyms s ]

sigSymsOf :: Sign f e -> [Symbol]
sigSymsOf s = concat
  [ Set.toList $ sortSyms s
  , map (\ (a, b) -> Symbol a $ SubsortAsItemType b)
    . Rel.toList . Rel.transReduce . Rel.irreflex $ sortRel s
    -- assume sort relation to be the transitive closure
  , opSyms s
  , predSyms s ]

-- | set of symbols for a signature
symsetOf :: Sign f e -> SymbolSet
symsetOf = Set.unions . symOf

checkSymbList :: [SYMB_OR_MAP] -> [Diagnosis]
checkSymbList l = case l of
         Symb (Symb_id a) : Symb (Qual_id b t _) : r -> mkDiag Warning
           ("profile '" ++ showDoc t "' does not apply to '"
            ++ showId a "' but only to") b : checkSymbList r
         _ : r -> checkSymbList r
         [] -> []

insertRsys :: (Pretty r, GetRange r, Ord r)
  => (r -> Id) -> (r -> Maybe Id) -> (Id -> r)
    -> (r -> Maybe Id) -> (Id -> r) -> Map.Map r r -> (r, r)
      -> Result (Map.Map r r)
insertRsys rawId getSort mkSort getImplicit mkImplicit m1 (rsy1, rsy2) =
  let m3 = Map.insert rsy1 rsy2 m1 in
        case Map.lookup rsy1 m1 of
          Nothing -> case getSort rsy1 of
            Just i ->
              case Map.lookup (mkImplicit i) m1 of
                Just r2 | Just (rawId rsy2) == getImplicit r2 ->
                  warning m1 ("ignoring separate mapping for sort " ++
                    show i) $ getRange i
                _ -> return m3
            Nothing -> case getImplicit rsy1 of
              Just i -> let rsy3 = mkSort i in case Map.lookup rsy3 m1 of
                Just r2 | Just (rawId rsy2) == getSort r2 ->
                  warning (Map.delete rsy3 m3)
                      ("ignoring extra mapping of sort " ++
                       show i) $ getRange i
                   {- this case cannot occur, because unkinded names cannot
                      follow kinded ones:
                      in "sort s |-> t, o |-> q" "o" will be a sort, too. -}
                _ -> return m3
              _ -> return m3
          Just rsy3 -> if rsy2 == rsy3 then
            hint m1 ("ignoring duplicate mapping of "
                       ++ showDoc rsy1 "") $ getRange rsy1 else
              plain_error m1 ("Symbol " ++ showDoc rsy1 " mapped twice to "
                ++ showDoc rsy2 " and " ++ showDoc rsy3 "") nullRange

statSymbMapItems :: Sign f e -> Maybe (Sign f e) -> [SYMB_MAP_ITEMS]
  -> Result RawSymbolMap
statSymbMapItems sig msig sl = do
  let st (Symb_map_items kind l _) = do
        appendDiags $ checkSymbList l
        fmap concat $ mapM (symbOrMapToRaw sig msig kind) l
      getSort rsy = case rsy of
        ASymbol (Symbol i SortAsItemType) -> Just i
        _ -> Nothing
      getImplicit rsy = case rsy of
        AKindedSymb Implicit i -> Just i
        _ -> Nothing
      mkSort i = ASymbol $ Symbol i SortAsItemType
      mkImplicit = AKindedSymb Implicit
  ls <- mapM st sl
  foldM (insertRsys rawSymName getSort mkSort getImplicit mkImplicit)
                    Map.empty (concat ls)

symbOrMapToRaw :: Sign f e -> Maybe (Sign f e) -> SYMB_KIND -> SYMB_OR_MAP
   -> Result [(RawSymbol, RawSymbol)]
symbOrMapToRaw sig msig k sm = case sm of
    Symb s -> do
      v <- symbToRaw True sig k s
      return [(v, v)]
    Symb_map s t _ -> do
      appendDiags $ case (s, t) of
        (Symb_id a, Symb_id b) | a == b ->
          [mkDiag Hint "unneeded identical mapping of" a]
        _ -> []
      w <- symbToRaw True sig k s
      x <- case msig of
             Nothing -> symbToRaw False sig k t
             Just tsig -> symbToRaw True tsig k t
      let mkS = ASymbol . idToSortSymbol
      case (s, t) of
        (Qual_id _ t1 _, Qual_id _ t2 _) -> case (t1, t2) of
          (O_type (Op_type _ args1 res1 _), O_type (Op_type _ args2 res2 _))
            | length args1 == length args2 -> -- ignore partiality
            return $ (w, x) : (mkS res1, mkS res2)
              : zipWith (\ s1 s2 -> (mkS s1, mkS s2)) args1 args2
          (P_type (Pred_type args1 _), P_type (Pred_type args2 _))
            | length args1 == length args2 ->
            return $ (w, x)
              : zipWith (\ s1 s2 -> (mkS s1, mkS s2)) args1 args2
          (O_type (Op_type _ [] res1 _), A_type s2) ->
            return [(w, x), (mkS res1, mkS s2)]
          (A_type s1, O_type (Op_type _ [] res2 _)) ->
            return [(w, x), (mkS s1, mkS res2)]
          (A_type s1, A_type s2) ->
            return [(w, x), (mkS s1, mkS s2)]
          _ -> Fail.fail $ "profiles '" ++ showDoc t1 "' and '"
               ++ showDoc t2 "' do not match"
        _ -> return [(w, x)]

statSymbItems :: Sign f e -> [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sig sl =
  let st (Symb_items kind l _) = do
        appendDiags $ checkSymbList $ map Symb l
        mapM (symbToRaw True sig kind) l
  in fmap concat (mapM st sl)

-- | bool indicates if a deeper symbol check is possible for target symbols
symbToRaw :: Bool -> Sign f e -> SYMB_KIND -> SYMB -> Result RawSymbol
symbToRaw b sig k si = case si of
  Symb_id idt -> return $ case k of
    Sorts_kind -> ASymbol $ idToSortSymbol idt
    _ -> AKindedSymb k idt
  Qual_id idt t _ -> typedSymbKindToRaw b sig k idt t

typedSymbKindToRaw :: Bool -> Sign f e -> SYMB_KIND -> Id -> TYPE
  -> Result RawSymbol
typedSymbKindToRaw b sig k idt t = let
     pm = predMap sig
     om = opMap sig
     getSet = MapSet.lookup idt
     err = plain_error (AKindedSymb Implicit idt)
              (showDoc idt ":" ++ showDoc t
               "does not have kind" ++ showDoc k "") (getRange idt)
     aSymb = ASymbol $ case t of
       O_type ot -> idToOpSymbol idt $ toOpType ot
       P_type pt -> idToPredSymbol idt $ toPredType pt
       A_type s -> idToOpSymbol idt $ sortToOpType s
     unKnown = do
       appendDiags [mkDiag Error "unknown symbol" aSymb]
       return aSymb
    in case k of
    Implicit -> case t of
      A_type s -> if b then do
          let pt = sortToPredType s
              ot = sortToOpType s
              pot = mkPartial ot
              hasPred = Set.member pt $ getSet pm
              hasOp = Set.member ot $ getSet om
              hasPOp = Set.member pot $ getSet om
              bothWarn = when hasPred $
                appendDiags [mkDiag Warning "considering operation only" idt]
          if hasOp then do
              appendDiags [mkDiag Hint "matched constant" idt]
              bothWarn
              return aSymb
            else if hasPOp then do
              bothWarn
              appendDiags [mkDiag Warning "constant is partial" idt]
              return $ ASymbol $ idToOpSymbol idt pot
            else if hasPred then do
              appendDiags [mkDiag Hint "matched unary predicate" idt]
              return $ ASymbol $ idToPredSymbol idt pt
            else unKnown
        else do
          appendDiags [mkDiag Warning "qualify name as pred or op" idt]
          return aSymb
      _ -> return aSymb
    Ops_kind -> case t of
        P_type _ -> err
        _ ->
          let ot = case t of
                     O_type aot -> toOpType aot
                     A_type s -> sortToOpType s
                     P_type _ -> error "CASL.typedSymbKindToRaw.Ops_kind"
              pot = mkPartial ot
              isMem aot = Set.member aot $ getSet om
          in if b then
            if isMem ot then return aSymb
            else if isMem pot then do
             appendDiags [mkDiag Warning "operation is partial" idt]
             return $ ASymbol $ idToOpSymbol idt pot
            else unKnown
          else return aSymb
    Preds_kind -> case t of
        O_type _ -> err
        _ ->
          let pt = case t of
                     A_type s -> sortToPredType s
                     P_type qt -> toPredType qt
                     O_type _ -> error "CASL.typedSymbKindToRaw.Preds_kind"
              pSymb = ASymbol $ idToPredSymbol idt pt
          in if b then
              if Set.member pt $ getSet pm then do
                 appendDiags [mkDiag Hint "matched predicate" idt]
                 return pSymb
              else unKnown
             else return pSymb
    Sorts_kind -> err

morphismToSymbMap :: Morphism f e m -> SymbolMap
morphismToSymbMap = morphismToSymbMapAux False

morphismToSymbMapAux :: Bool -> Morphism f e m -> SymbolMap
morphismToSymbMapAux b mor = let
    src = msource mor
    sorts = sort_map mor
    ops = op_map mor
    preds = pred_map mor
    sortSymMap = Set.fold
      (\ s -> let t = mapSort sorts s in
         if b && s == t then id else
             Map.insert (idToSortSymbol s) $ idToSortSymbol t)
      Map.empty $ sortSet src
    opSymMap = MapSet.foldWithKey
      ( \ i t -> let (j, k) = mapOpSym sorts ops (i, t) in
                 if b && i == j && opKind k == opKind t then id else
                     Map.insert (idToOpSymbol i t) $ idToOpSymbol j k)
      Map.empty $ opMap src
    predSymMap = MapSet.foldWithKey
      ( \ i t -> let (j, k) = mapPredSym sorts preds (i, t) in
                 if b && i == j then id else
                     Map.insert (idToPredSymbol i t) $ idToPredSymbol j k)
      Map.empty $ predMap src
  in foldr Map.union sortSymMap [opSymMap, predSymMap]

matches :: Symbol -> RawSymbol -> Bool
matches (Symbol idt k) rs = case rs of
    ASymbol (Symbol id2 k2) -> idt == id2 && case (k, k2) of
     (OpAsItemType ot, OpAsItemType ot2) -> compatibleOpTypes ot ot2
     _ -> k == k2
    AKindedSymb rk di -> let res = idt == di in case (k, rk) of
        (_, Implicit) -> res
        (SortAsItemType, Sorts_kind) -> res
        (OpAsItemType _, Ops_kind) -> res
        (PredAsItemType _, Preds_kind) -> res
        _ -> False

idMor :: m -> Sign f e -> Morphism f e m
idMor extEm sigma = embedMorphism extEm sigma sigma

composeM :: Eq e => (Morphism f e m -> Morphism f e m -> Result m)
         -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
composeM comp mor1 mor2 = do
  let sMap1 = sort_map mor1
      src = msource mor1
      tar = mtarget mor2
      oMap1 = op_map mor1
      pMap1 = pred_map mor1
      sMap2 = sort_map mor2
      oMap2 = op_map mor2
      pMap2 = pred_map mor2
      sMap = composeMap (MapSet.setToMap $ sortSet src) sMap1 sMap2
      oMap = if Map.null oMap2 then oMap1 else
                 MapSet.foldWithKey ( \ i ot ->
                       let (ni, nt) = mapOpSym sMap2 oMap2
                             $ mapOpSym sMap1 oMap1 (i, ot)
                           k = opKind nt
                       in if i == ni && opKind ot == k then id else
                          Map.insert (i, mkPartial ot) (ni, k))
                     Map.empty $ opMap src
      pMap = if Map.null pMap2 then pMap1 else
                 MapSet.foldWithKey ( \ i pt ->
                       let ni = fst $ mapPredSym sMap2 pMap2
                             $ mapPredSym sMap1 pMap1 (i, pt)
                       in if i == ni then id else Map.insert (i, pt) ni)
                      Map.empty $ predMap src
  extComp <- comp mor1 mor2
  let emb = embedMorphism extComp src tar
  return $ cleanMorMaps emb
     { sort_map = sMap
     , op_map = oMap
     , pred_map = pMap }

legalSign :: Sign f e -> Bool
legalSign sigma =
  MapSet.setAll legalSort (MapSet.setElems . Rel.toMap $ sortRel sigma)
  && MapSet.all legalOpType (opMap sigma)
  && MapSet.all legalPredType (predMap sigma)
  where sorts = sortSet sigma
        legalSort s = Set.member s sorts
        legalOpType t = -- omitted for VSE Boolean: legalSort (opRes t)
                        all legalSort (opArgs t)
        legalPredType = all legalSort . predArgs

-- | the image of a signature morphism
imageOfMorphism :: Morphism f e m -> Sign f e
imageOfMorphism m = imageOfMorphismAux (const $ extendedInfo $ mtarget m) m

-- | the generalized image of a signature morphism
imageOfMorphismAux :: (Morphism f e m -> e) -> Morphism f e m -> Sign f e
imageOfMorphismAux fE m =
  inducedSignAux (\ _ _ _ _ _ -> fE m)
         (sort_map m) (op_map m) (pred_map m) (extended_map m) (msource m)

type InducedSign f e m r =
  Sort_map -> Op_map -> Pred_map -> m -> Sign f e -> r

-- | the induced signature image of a signature morphism
inducedSignAux :: InducedSign f e m e -> InducedSign f e m (Sign f e)
inducedSignAux f sm om pm em src =
  let ms = mapSort sm
      msorts = Set.map ms
  in (emptySign $ f sm om pm em src)
  { sortRel = Rel.transClosure . Rel.irreflex . Rel.map ms $ sortRel src
    -- sorts may fall together and need to be removed as trivial relation
  , emptySortSet = msorts $ emptySortSet src
  , opMap = inducedOpMap sm om $ opMap src
  , assocOps = inducedOpMap sm om $ assocOps src
  , predMap = inducedPredMap sm pm $ predMap src
  , annoMap = inducedAnnoMap sm om pm $ annoMap src
  }

inducedOpMap :: Sort_map -> Op_map -> OpMap -> OpMap
inducedOpMap sm fm = MapSet.foldWithKey
  (\ i ot -> let (j, nt) = mapOpSym sm fm (i, ot)
     in MapSet.insert j nt) MapSet.empty

inducedPredMap :: Sort_map -> Pred_map -> PredMap -> PredMap
inducedPredMap sm pm = MapSet.foldWithKey
  ( \ i pt -> let (j, nt) = mapPredSym sm pm (i, pt)
      in MapSet.insert j nt) MapSet.empty

inducedAnnoMap :: Sort_map -> Op_map -> Pred_map -> AnnoMap -> AnnoMap
inducedAnnoMap sm om pm = MapSet.foldWithKey
  ( \ sy s -> MapSet.insert (mapSymbol sm om pm sy) s) MapSet.empty

mapSymbol :: Sort_map -> Op_map -> Pred_map -> Symbol -> Symbol
mapSymbol sm om pm (Symbol i ty) = case ty of
  SortAsItemType -> Symbol (mapSort sm i) SortAsItemType
  SubsortAsItemType j ->
    Symbol (mapSort sm i) $ SubsortAsItemType $ mapSort sm j
  OpAsItemType ot -> let (j, nt) = mapOpSym sm om (i, ot) in
    Symbol j $ OpAsItemType nt
  PredAsItemType pt -> let (j, nt) = mapPredSym sm pm (i, pt) in
    Symbol j $ PredAsItemType nt

legalMor :: MorphismExtension e m => Morphism f e m -> Result ()
legalMor mor =
  let s1 = msource mor
      s2 = mtarget mor
      sm = sort_map mor
      msorts = Set.map $ mapSort sm
  in if legalSign s1
  && Set.isSubsetOf (msorts $ sortSet s1) (sortSet s2)
  && Set.isSubsetOf (msorts $ emptySortSet s1) (emptySortSet s2)
  && isSubOpMap (inducedOpMap sm (op_map mor) $ opMap s1) (opMap s2)
  && isSubMap (inducedPredMap sm (pred_map mor) $ predMap s1) (predMap s2)
  && legalSign s2
  then legalMorphismExtension mor else Fail.fail "illegal CASL morphism"

isInclOpMap :: Op_map -> Bool
isInclOpMap = all (\ ((i, _), (j, _)) -> i == j) . Map.toList

idOrInclMorphism :: Morphism f e m -> Morphism f e m
idOrInclMorphism m =
  let src = opMap $ msource m
      tar = opMap $ mtarget m
  in if isSubOpMap tar src then m
     else let diffOpMap = MapSet.toMap $ MapSet.difference src tar in
          m { op_map = Map.fromList $ concatMap (\ (i, s) ->
              map (\ t -> ((i, t), (i, Total)))
                 $ Set.toList s) $ Map.toList diffOpMap }

sigInclusion :: m -- ^ computed extended morphism
             -> Sign f e -> Sign f e -> Result (Morphism f e m)
sigInclusion extEm sigma1 =
     return . idOrInclMorphism . embedMorphism extEm sigma1

addSigM :: Monad m => (e -> e -> m e) -> Sign f e -> Sign f e -> m (Sign f e)
addSigM f a b = do
  e <- f (extendedInfo a) $ extendedInfo b
  return $ addSig (const $ const e) a b

plainMorphismUnion :: (e -> e -> e) -- ^ join signature extensions
  -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
plainMorphismUnion = morphismUnion retExtMap

retExtMap :: b -> Morphism f e m -> Result m
retExtMap = const $ return . extended_map

morphismUnion :: (Morphism f e m -> Morphism f e m -> Result m)
  -- ^ join morphism extensions
  -> (e -> e -> e) -- ^ join signature extensions
  -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
morphismUnion uniteM addSigExt =
    morphismUnionM uniteM (\ e -> return . addSigExt e)

morphismUnionM :: (Morphism f e m -> Morphism f e m -> Result m)
 -- ^ join morphism extensions
 -> (e -> e -> Result e) -- ^ join signature extensions
 -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
-- consider identity mappings but filter them eventually
morphismUnionM uniteM addSigExt mor1 mor2 =
  let smap1 = sort_map mor1
      smap2 = sort_map mor2
      s1 = msource mor1
      s2 = msource mor2
      us1 = Set.difference (sortSet s1) $ Map.keysSet smap1
      us2 = Set.difference (sortSet s2) $ Map.keysSet smap2
      omap1 = op_map mor1
      omap2 = op_map mor2
      uo1 = foldr delOp (opMap s1) $ Map.keys omap1
      uo2 = foldr delOp (opMap s2) $ Map.keys omap2
      delOp (n, ot) m = diffOpMapSet m $ MapSet.fromList [(n, [mkTotal ot])]
      uo = addOpMapSet uo1 uo2
      pmap1 = pred_map mor1
      pmap2 = pred_map mor2
      up1 = foldr delPred (predMap s1) $ Map.keys pmap1
      up2 = foldr delPred (predMap s2) $ Map.keys pmap2
      up = addMapSet up1 up2
      delPred (n, pt) = MapSet.delete n pt
      (sds, smap) = foldr ( \ (i, j) (ds, m) -> case Map.lookup i m of
          Nothing -> (ds, Map.insert i j m)
          Just k -> if j == k then (ds, m) else
              (Diag Error
               ("incompatible mapping of sort " ++ showId i " to "
                ++ showId j " and " ++ showId k "")
               nullRange : ds, m)) ([], smap1)
          (Map.toList smap2 ++ map (\ a -> (a, a))
                      (Set.toList $ Set.union us1 us2))
      (ods, omap) = foldr ( \ (isc@(i, ot), jsc@(j, t)) (ds, m) ->
          case Map.lookup isc m of
          Nothing -> (ds, Map.insert isc jsc m)
          Just (k, p) -> if j == k then if p == t then (ds, m)
                            else (ds, Map.insert isc (j, Total) m) else
              (Diag Error
               ("incompatible mapping of op " ++ showId i ":"
                ++ showDoc (setOpKind t ot) " to "
                ++ showId j " and " ++ showId k "") nullRange : ds, m))
           (sds, omap1) (Map.toList omap2 ++ map
              ( \ (a, ot) -> ((a, mkPartial ot), (a, opKind ot)))
              (mapSetToList uo))
      (pds, pmap) = foldr ( \ (isc@(i, pt), j) (ds, m) ->
          case Map.lookup isc m of
          Nothing -> (ds, Map.insert isc j m)
          Just k -> if j == k then (ds, m) else
              (Diag Error
               ("incompatible mapping of pred " ++ showId i ":"
                ++ showDoc pt " to " ++ showId j " and "
                ++ showId k "") nullRange : ds, m)) (ods, pmap1)
          (Map.toList pmap2 ++ map ( \ (a, pt) -> ((a, pt), a))
                  (mapSetToList up))
  in if null pds then do
    s3 <- addSigM addSigExt s1 s2
    s4 <- addSigM addSigExt (mtarget mor1) $ mtarget mor2
    extM <- uniteM mor1 mor2
    return $ cleanMorMaps
      (embedMorphism extM s3 s4)
      { sort_map = smap
      , op_map = omap
      , pred_map = pmap }
    else Result pds Nothing

cleanMorMaps :: Morphism f e m -> Morphism f e m
cleanMorMaps m = m
  { sort_map = Map.filterWithKey (/=) $ sort_map m
  , op_map = Map.filterWithKey
        (\ (i, ot) (j, k) -> i /= j || k == Total && Set.member ot
         (MapSet.lookup i $ opMap $ msource m)) $ op_map m
  , pred_map = Map.filterWithKey ((/=) . fst) $ pred_map m }

isSortInjective :: Morphism f e m -> Bool
isSortInjective m =
    let ss = sortSet $ msource m
    in Set.size ss == Set.size (Set.map (mapSort $ sort_map m) ss)

sumSize :: MapSet.MapSet a b -> Int
sumSize = sum . map Set.size . Map.elems . MapSet.toMap

-- morphism extension m is not considered here
isInjective :: Morphism f e m -> Bool
isInjective m = isSortInjective m && let
    src = msource m
    sm = sort_map m
    os = opMap src
    ps = predMap src
    in sumSize os == sumSize (inducedOpMap sm (op_map m) os)
       && sumSize ps == sumSize (inducedPredMap sm (pred_map m) ps)

instance Pretty RawSymbol where
  pretty rsym = case rsym of
    ASymbol sy -> pretty sy
    AKindedSymb k i -> pretty k <+> pretty i

printMorphism :: (e -> e -> Bool) -> (m -> Bool) -> (e -> Doc)
  -> (Morphism f e m -> Doc) -> Morphism f e m -> Doc
printMorphism isSubSigExt isInclMorExt fE fM mor =
    let src = msource mor
        tar = mtarget mor
        ops = op_map mor
        prSig s = specBraces (space <> printSign fE s)
        srcD = prSig src
    in fsep $ if isInclusionMorphism isInclMorExt mor then
              if isSubSig isSubSigExt tar src then
                  [text "identity morphism over", srcD]
              else
                  [text "inclusion morphism of", srcD
                 , if Map.null ops then empty
                   else fsep
                   [text "by totalizing",
                    pretty $ Set.map (uncurry idToOpSymbol) $ Map.keysSet ops]]
    else
      [ braces $ printMap id sepByCommas pairElems
          (morphismToSymbMapAux True mor) $+$ fM mor
      , colon <+> srcD, mapsto <+> prSig tar ]

instance (SignExtension e, Pretty e, Show f, MorphismExtension e m)
  => Pretty (Morphism f e m) where
       pretty = printMorphism isSubSignExtension isInclusionMorphismExtension
         pretty prettyMorphismExtension

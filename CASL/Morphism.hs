{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies
  , FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Symbols and signature morphisms for the CASL logic
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC+FD)

Symbols and signature morphisms for the CASL logic
-}

module CASL.Morphism where

import CASL.Sign
import CASL.AS_Basic_CASL

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils (composeMap)

import Control.Monad

type SymbolSet = Set.Set Symbol
type SymbolMap = Map.Map Symbol Symbol

data RawSymbol = ASymbol Symbol | AKindedSymb SYMB_KIND Id
                 deriving (Show, Eq, Ord)

instance GetRange RawSymbol where
    getRange rs = case rs of
        ASymbol s -> getRange s
        AKindedSymb _ i -> getRange i

type RawSymbolSet = Set.Set RawSymbol
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
  } deriving (Show, Eq, Ord)

data DefMorExt e = DefMorExt e

instance Show (DefMorExt e) where
  show = const ""

instance Ord (DefMorExt e) where
  compare _ = const EQ

instance Eq (DefMorExt e) where
  (==) e = (== EQ) . compare e

emptyMorExt :: DefMorExt e
emptyMorExt = DefMorExt $ error "emptyMorExt"

instance Show e => Pretty (DefMorExt e) where
  pretty _ = empty

class MorphismExtension e m | m -> e where
   ideMorphismExtension :: e -> m
   composeMorphismExtension :: e -> m -> m -> Result m
   inverseMorphismExtension :: m -> Result m
   isInclusionMorphismExtension :: m -> Bool

instance MorphismExtension () () where
   ideMorphismExtension _ = ()
   composeMorphismExtension _ _ = return
   inverseMorphismExtension = return
   isInclusionMorphismExtension _ = True

instance MorphismExtension e (DefMorExt e) where
   ideMorphismExtension _ = emptyMorExt
   composeMorphismExtension _ _ = return
   inverseMorphismExtension = return
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

mapOpTypeK :: Sort_map -> OpKind -> OpType -> OpType
mapOpTypeK sorts k = makeTotal k . mapOpType sorts

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
compatibleOpTypes ot1 ot2 = opArgs ot1 == opArgs ot2 && opRes ot1 == opRes ot2

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

symbTypeToKind :: SymbType -> SYMB_KIND
symbTypeToKind st = case st of
  OpAsItemType _ -> Ops_kind
  PredAsItemType _ -> Preds_kind
  SortAsItemType -> Sorts_kind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw = ASymbol

idToRaw :: Id -> RawSymbol
idToRaw = AKindedSymb Implicit

rawSymName :: RawSymbol -> Id
rawSymName rs = case rs of
  ASymbol sym -> symName sym
  AKindedSymb _ i -> i

allSymOf :: (e -> SymbolSet) -> Sign f e -> [SymbolSet]
allSymOf f s = let (s1, so) = Set.partition ((== Sorts_kind) .
                                             symbTypeToKind . symbType)
                              $ f (extendedInfo s)
               in zipWith Set.union (symPair s) [s1, so]

symPair :: Sign f e -> [SymbolSet]
symPair sigma =
    let
        ml f = concatMap (\ (i, ts) -> map (f i) $ Set.toList ts) . Map.toList
        sorts = Set.map idToSortSymbol $ sortSet sigma
        ops = ml idToOpSymbol $ opMap sigma
        preds = ml idToPredSymbol $ predMap sigma
    in [sorts, Set.fromList $ ops ++ preds]

{- | returns the symbol sets of the signature in the correct dependency order
, i.e., sorts first, then ops and predicates. Result list is of length two. -}
symOf :: Sign f e -> [SymbolSet]
symOf = symPair

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

statSymbMapItems :: [SYMB_MAP_ITEMS] -> Result RawSymbolMap
statSymbMapItems sl = do
  let st (Symb_map_items kind l _) = do
        appendDiags $ checkSymbList l
        fmap concat $ mapM (symbOrMapToRaw kind) l
      insertRsys m1 (rsy1, rsy2) = let m3 = Map.insert rsy1 rsy2 m1 in
        case Map.lookup rsy1 m1 of
          Nothing -> case rsy1 of
            ASymbol (Symbol i SortAsItemType) ->
              case Map.lookup (AKindedSymb Implicit i) m1 of
                Just (AKindedSymb Implicit j) | rawSymName rsy2 == j ->
                  warning m1 ("ignoring separate mapping for sort " ++
                    show i) $ getRange i
                _ -> return m3
            AKindedSymb Implicit i ->
              let rsy3 = ASymbol (Symbol i SortAsItemType) in
              case Map.lookup rsy3 m1 of
                Just (ASymbol (Symbol j SortAsItemType))
                  | rawSymName rsy2 == j -> warning (Map.delete rsy3 m3)
                      ("ignoring extra mapping of sort " ++
                       show i) $ getRange j
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
  ls <- mapM st sl
  foldM insertRsys Map.empty (concat ls)

symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> Result [(RawSymbol, RawSymbol)]
symbOrMapToRaw k sm = case sm of
    Symb s -> do
      v <- symbToRaw k s
      return [(v, v)]
    Symb_map s t _ -> do
      appendDiags $ case (s, t) of
        (Symb_id a, Symb_id b) | a == b ->
          [mkDiag Hint "unneeded identical mapping of" a]
        _ -> []
      w <- symbToRaw k s
      x <- symbToRaw k t
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
          _ -> fail $ "profiles '" ++ showDoc t1 "' and '"
               ++ showDoc t2 "' do not match"
        _ -> return [(w, x)]

statSymbItems :: [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sl =
  let st (Symb_items kind l _) = do
        appendDiags $ checkSymbList $ map Symb l
        mapM (symbToRaw kind) l
  in fmap concat (mapM st sl)

symbToRaw :: SYMB_KIND -> SYMB -> Result RawSymbol
symbToRaw k si = case si of
  Symb_id idt -> return $ case k of
    Sorts_kind -> ASymbol $ idToSortSymbol idt
    _ -> AKindedSymb k idt
  Qual_id idt t _ -> typedSymbKindToRaw k idt t

typedSymbKindToRaw :: SYMB_KIND -> Id -> TYPE -> Result RawSymbol
typedSymbKindToRaw k idt t = let
     err = plain_error (AKindedSymb Implicit idt)
              (showDoc idt ":" ++ showDoc t
               "does not have kind" ++ showDoc k "") nullRange
     aSymb = ASymbol $ case t of
       O_type ot -> idToOpSymbol idt $ toOpType ot
       P_type pt -> idToPredSymbol idt $ toPredType pt
             {- in case of ambiguity, return a constant function type
             this deviates from the CASL summary !!! -}
       A_type s ->
           let ot = OpType {opKind = Total, opArgs = [], opRes = s}
           in idToOpSymbol idt ot
    in case k of
    Implicit -> case t of
      A_type _ -> do
          appendDiags [mkDiag Warning "qualify name as pred or op" idt]
          return aSymb
      _ -> return aSymb
    Ops_kind -> case t of
        P_type _ -> err
        _ -> return aSymb
    Preds_kind -> case t of
        O_type _ -> err
        A_type s -> return $ ASymbol $
                    let pt = PredType {predArgs = [s]}
                    in idToPredSymbol idt pt
        P_type _ -> return aSymb
    _ -> err

morphismToSymbMap :: Morphism f e m -> SymbolMap
morphismToSymbMap = morphismToSymbMapAux False

extMorphismToSymbMap :: (e -> m -> SymbolMap) -> Morphism f e m -> SymbolMap
extMorphismToSymbMap extM m =
  Map.union (extM (extendedInfo $ msource m) $ extended_map m)
     $ morphismToSymbMap m

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
    opSymMap = Map.foldWithKey
      ( \ i s m -> Set.fold
        ( \ t -> let (j, k) = mapOpSym sorts ops (i, t) in
                 if b && i == j && opKind k == opKind t then id else
                     Map.insert (idToOpSymbol i t) $ idToOpSymbol j k)
        m s) Map.empty $ opMap src
    predSymMap = Map.foldWithKey
      ( \ i s m -> Set.fold
        ( \ t -> let (j, k) = mapPredSym sorts preds (i, t) in
                 if b && i == j then id else
                     Map.insert (idToPredSymbol i t) $ idToPredSymbol j k)
        m s) Map.empty $ predMap src
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

composeM :: Eq e => (m -> m -> Result m)
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
      sMap = composeMap (Rel.setToMap $ sortSet src) sMap1 sMap2
      oMap = if Map.null oMap2 then oMap1 else
                 Map.foldWithKey ( \ i t m ->
                   Set.fold ( \ ot ->
                       let (ni, nt) = mapOpSym sMap2 oMap2
                             $ mapOpSym sMap1 oMap1 (i, ot)
                           k = opKind nt
                       in if i == ni && opKind ot == k then id else
                          Map.insert (i, mkPartial ot) (ni, k)) m t)
                     Map.empty $ opMap src
      pMap = if Map.null pMap2 then pMap1 else
                 Map.foldWithKey ( \ i t m ->
                   Set.fold ( \ pt ->
                       let ni = fst $ mapPredSym sMap2 pMap2
                             $ mapPredSym sMap1 pMap1 (i, pt)
                       in if i == ni then id else Map.insert (i, pt) ni) m t)
                      Map.empty $ predMap src
  extComp <- comp (extended_map mor1) $ extended_map mor2
  let emb = embedMorphism extComp src tar
  return $ cleanMorMaps emb
     { sort_map = sMap
     , op_map = oMap
     , pred_map = pMap }

legalSign :: Sign f e -> Bool
legalSign sigma =
  Map.foldWithKey (\ s sset -> (&& legalSort s && all legalSort
                                (Set.toList sset)))
                  True (Rel.toMap (sortRel sigma))
  && Map.fold (\ ts -> (&& all legalOpType (Set.toList ts)))
              True (opMap sigma)
  && Map.fold (\ ts -> (&& all legalPredType (Set.toList ts)))
              True (predMap sigma)
  where sorts = sortSet sigma
        legalSort s = Set.member s sorts
        legalOpType t = legalSort (opRes t)
                        && all legalSort (opArgs t)
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
  { sortSet = msorts $ sortSet src
  , sortRel = Rel.map ms $ sortRel src
  , emptySortSet = msorts $ emptySortSet src
  , opMap = inducedOpMap sm om $ opMap src
  , assocOps = inducedOpMap sm om $ assocOps src
  , predMap = inducedPredMap sm pm $ predMap src }

inducedOpMap :: Sort_map -> Op_map -> OpMap -> OpMap
inducedOpMap sm fm = Map.foldWithKey
  ( \ i -> flip $ Set.fold ( \ ot ->
      let (j, nt) = mapOpSym sm fm (i, ot)
      in Rel.setInsert j nt)) Map.empty

inducedPredMap :: Sort_map -> Pred_map -> Map.Map Id (Set.Set PredType)
               -> Map.Map Id (Set.Set PredType)
inducedPredMap sm pm = Map.foldWithKey
  ( \ i -> flip $ Set.fold ( \ ot ->
      let (j, nt) = mapPredSym sm pm (i, ot)
      in Rel.setInsert j nt)) Map.empty

legalMor :: Morphism f e m -> Bool
legalMor mor =
  let s1 = msource mor
      s2 = mtarget mor
      sm = sort_map mor
      msorts = Set.map $ mapSort sm
  in legalSign s1
  && Set.isSubsetOf (msorts $ sortSet s1) (sortSet s2)
  && Set.isSubsetOf (msorts $ emptySortSet s1) (emptySortSet s2)
  && isSubOpMap (inducedOpMap sm (op_map mor) $ opMap s1) (opMap s2)
  && isSubMapSet (inducedPredMap sm (pred_map mor) $ predMap s1) (predMap s2)
  && legalSign s2

isInclOpMap :: Op_map -> Bool
isInclOpMap = all (\ ((i, _), (j, k)) -> i == j && k == Total) . Map.toList

idOrInclMorphism :: Morphism f e m -> Morphism f e m
idOrInclMorphism m =
  let src = opMap $ msource m
      tar = opMap $ mtarget m
  in if isSubOpMap tar src then m
     else let diffOpMap = diffMapSet src tar in
          m { op_map = Map.fromList $ concatMap (\ (i, s) ->
              map (\ t -> ((i, t), (i, Total)))
                 $ Set.toList s) $ Map.toList diffOpMap }

sigInclusion :: (Pretty f, Pretty e)
             => m -- ^ computed extended morphism
             -> Sign f e -> Sign f e -> Result (Morphism f e m)
sigInclusion extEm sigma1 =
     return . idOrInclMorphism . embedMorphism extEm sigma1

addSigM :: Monad m => (e -> e -> m e) -> Sign f e -> Sign f e -> m (Sign f e)
addSigM f a b = do
  e <- f (extendedInfo a) $ extendedInfo b
  return $ addSig (const $ const e) a b

morphismUnion :: (m -> m -> m) -- ^ join morphism extensions
              -> (e -> e -> e) -- ^ join signature extensions
              -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
morphismUnion uniteM addSigExt =
    morphismUnionM uniteM (\ e -> return . addSigExt e)

morphismUnionM :: (m -> m -> m)  -- ^ join morphism extensions
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
      delOp (n, ot) m = diffMapSet m $ Map.singleton n $
                    Set.fromList [mkPartial ot, mkTotal ot]
      uo = addOpMapSet uo1 uo2
      pmap1 = pred_map mor1
      pmap2 = pred_map mor2
      up1 = foldr delPred (predMap s1) $ Map.keys pmap1
      up2 = foldr delPred (predMap s2) $ Map.keys pmap2
      up = addMapSet up1 up2
      delPred (n, pt) m = diffMapSet m $ Map.singleton n $ Set.singleton pt
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
                ++ showDoc ot { opKind = t } " to "
                ++ showId j " and " ++ showId k "") nullRange : ds, m))
           (sds, omap1) (Map.toList omap2 ++ concatMap
              ( \ (a, s) -> map ( \ ot -> ((a, mkPartial ot),
                                           (a, opKind ot)))
              $ Set.toList s) (Map.toList uo))
      (pds, pmap) = foldr ( \ (isc@(i, pt), j) (ds, m) ->
          case Map.lookup isc m of
          Nothing -> (ds, Map.insert isc j m)
          Just k -> if j == k then (ds, m) else
              (Diag Error
               ("incompatible mapping of pred " ++ showId i ":"
                ++ showDoc pt " to " ++ showId j " and "
                ++ showId k "") nullRange : ds, m)) (ods, pmap1)
          (Map.toList pmap2 ++ concatMap ( \ (a, s) -> map
              ( \ pt -> ((a, pt), a)) $ Set.toList s) (Map.toList up))
  in if null pds then do
    s3 <- addSigM addSigExt s1 s2
    s4 <- addSigM addSigExt (mtarget mor1) $ mtarget mor2
    return $ cleanMorMaps
      (embedMorphism (uniteM (extended_map mor1) $ extended_map mor2) s3 s4)
      { sort_map = smap
      , op_map = omap
      , pred_map = pmap }
    else Result pds Nothing

cleanMorMaps :: Morphism f e m -> Morphism f e m
cleanMorMaps m = m
  { sort_map = Map.filterWithKey (/=) $ sort_map m
  , op_map = Map.filterWithKey
        (\ (i, ot) (j, k) -> i /= j || k == Total && Set.member ot
         (Map.findWithDefault Set.empty i $ opMap $ msource m)) $ op_map m
  , pred_map = Map.filterWithKey ((/=) . fst) $ pred_map m }

isSortInjective :: Morphism f e m -> Bool
isSortInjective m =
    let ss = sortSet $ msource m
    in Set.size ss == Set.size (Set.map (mapSort $ sort_map m) ss)

sumSize :: Map.Map a (Set.Set b) -> Int
sumSize = sum . map Set.size . Map.elems

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

printMorphism :: (e -> e -> Bool) -> (m -> Bool) -> (e -> Doc) -> (m -> Doc)
  -> (e -> SymbolSet) -> Morphism f e m -> Doc
printMorphism isSubSigExt isInclMorExt fE fM symOfExt mor =
    let src = msource mor
        tar = mtarget mor
        ops = op_map mor
        prSig s = specBraces (space <> printSign fE s)
        srcD = prSig src
    in if isInclusionMorphism isInclMorExt mor then
           if isSubSig isSubSigExt tar src then
               fsep [text "identity morphism over", srcD]
           else fsep
      [ text "inclusion morphism of", srcD
      , fsep $ if Map.null ops then
          [ text "extended with"
          , pretty $ Set.unions $ zipWith Set.difference (allSymOf symOfExt tar)
                       $ allSymOf symOfExt src ]
        else
          [ text "by totalizing"
          , pretty $ Set.map (uncurry idToOpSymbol) $ Map.keysSet ops ]]
    else fsep
      [ pretty (morphismToSymbMapAux True mor)
          $+$ fM (extended_map mor)
      , colon <+> srcD, mapsto <+> prSig tar ]

instance (SignExtension e, Pretty e, Show f, MorphismExtension e m, Pretty m)
  => Pretty (Morphism f e m) where
       pretty = printMorphism isSubSignExtension isInclusionMorphismExtension
         pretty pretty symOfExtension

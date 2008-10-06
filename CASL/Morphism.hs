{- |
Module      :  $Header$
Description :  Symbols and signature morphisms for the CASL logic
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

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
import Common.Keywords
import Common.Result

import Control.Exception (assert)
import Control.Monad

type SymbolSet = Set.Set Symbol
type SymbolMap = Map.Map Symbol Symbol

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
                 deriving (Show, Eq, Ord)

instance GetRange RawSymbol where
    getRange rs = case rs of
        ASymbol s -> getRange s
        AnID i -> getRange i
        AKindedId _ i -> getRange i

type RawSymbolSet = Set.Set RawSymbol
type RawSymbolMap = Map.Map RawSymbol RawSymbol

data Kind = SortKind | FunKind | PredKind deriving (Show, Eq, Ord)

type Sort_map = Map.Map SORT SORT
-- always use the partial profile as key!
type Fun_map = Map.Map (Id, OpType) (Id, FunKind)
type Pred_map = Map.Map (Id, PredType) Id
type CASLMor = Morphism () () ()

data MorKind = IdMor | InclMor | OtherMor deriving (Show, Eq, Ord)

data Morphism f e m = Morphism
  { msource :: Sign f e
  , mtarget :: Sign f e
  , morKind :: MorKind
  , sort_map :: Sort_map
  , fun_map :: Fun_map
  , pred_map :: Pred_map
  , extended_map :: m
  } deriving Show

isInclusionMorphism :: Morphism f e m -> Bool
isInclusionMorphism m = morKind m <= InclMor

instance (Eq f, Eq e, Eq m) => Eq (Morphism f e m) where
    m1 == m2 = msource m1 == msource m2 &&
      (morKind m1 == IdMor && morKind m2 == IdMor
       || mtarget m1 == mtarget m2) &&
      sort_map m1 == sort_map m2 &&
      fun_map m1 == fun_map m2 &&
      pred_map m1 == pred_map m2 &&
      extended_map m1 == extended_map m2

mapSort :: Sort_map -> SORT -> SORT
mapSort sorts s = Map.findWithDefault s s sorts

mapOpType :: Sort_map -> OpType -> OpType
mapOpType sorts t = if Map.null sorts then t else
  t { opArgs = map (mapSort sorts) $ opArgs t
    , opRes = mapSort sorts $ opRes t }

mapOpTypeK :: Sort_map -> FunKind -> OpType -> OpType
mapOpTypeK sorts k t = makeTotal k $ mapOpType sorts t

makeTotal :: FunKind -> OpType -> OpType
makeTotal fk t = case fk of
  Total -> t { opKind = Total }
  _ -> t

mapOpSym :: Sort_map -> Fun_map -> (Id, OpType) -> (Id, OpType)
mapOpSym sMap fMap (i, ot) = let mot = mapOpType sMap ot in
  case Map.lookup (i, ot {opKind = Partial} ) fMap of
    Nothing -> (i, mot)
    Just (j, k) -> (j, makeTotal k mot)

-- | Check if two OpTypes are equal modulo totality or partiality
compatibleOpTypes :: OpType -> OpType -> Bool
compatibleOpTypes ot1 ot2 = opArgs ot1 == opArgs ot2 && opRes ot1 == opRes ot2

mapPredType :: Sort_map -> PredType -> PredType
mapPredType sorts t = if Map.null sorts then t else
  t { predArgs = map (mapSort sorts) $ predArgs t }

mapPredSym :: Sort_map -> Pred_map -> (Id, PredType) -> (Id, PredType)
mapPredSym sMap fMap (i, pt) =
    (Map.findWithDefault i (i, pt) fMap, mapPredType sMap pt)

embedMorphism :: m -> Sign f e -> Sign f e -> Morphism f e m
embedMorphism extEm a b = Morphism
  { msource = a
  , mtarget = b
  , morKind = OtherMor  -- unknown for most uses
  , sort_map = Map.empty
  , fun_map = Map.empty
  , pred_map = Map.empty
  , extended_map = extEm }

symbTypeToKind :: SymbType -> Kind
symbTypeToKind st = case st of
  OpAsItemType _ -> FunKind
  PredAsItemType _ -> PredKind
  SortAsItemType -> SortKind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw sym = ASymbol sym

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> Id
rawSymName rs = case rs of
  ASymbol sym -> symName sym
  AnID i -> i
  AKindedId _ i -> i

symOf :: Sign f e -> SymbolSet
symOf sigma = let
    sorts = Set.map idToSortSymbol $ sortSet sigma
    ops = Set.fromList $
      concatMap (\ (i, ts) -> map ( \ t -> idToOpSymbol i t) $ Set.toList ts)
        $ Map.toList $ opMap sigma
    preds = Set.fromList $
       concatMap (\ (i, ts) -> map ( \ t -> idToPredSymbol i t)
           $ Set.toList ts) $ Map.toList $ predMap sigma
    in Set.unions [sorts, ops, preds]

statSymbMapItems :: [SYMB_MAP_ITEMS] -> Result RawSymbolMap
statSymbMapItems sl = do
  let check l = case l of
         Symb (Symb_id _) : Symb (Qual_id b _ _) : r ->
            mkDiag Warning "qualification only applies to" b : check r
         _ : r -> check r
         [] -> []
      st (Symb_map_items kind l _) = do
        appendDiags $ check l
        mapM (symbOrMapToRaw kind) l
      insertRsys m1 (rsy1, rsy2) = case Map.lookup rsy1 m1 of
          Nothing -> return $ Map.insert rsy1 rsy2 m1
          Just rsy3 ->
              plain_error m1 ("Symbol " ++ showDoc rsy1 " mapped twice to "
                ++ showDoc rsy2 " and " ++ showDoc rsy3 "") nullRange
  ls <- mapM st sl
  foldM insertRsys Map.empty (concat ls)

symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> Result (RawSymbol, RawSymbol)
symbOrMapToRaw k sm = do
  let (u, v) = case sm of
         Symb s -> (s, s)
         Symb_map s t _ -> (s, t)
      ws = case sm of
             Symb_map (Symb_id a) (Symb_id b) _ | a == b ->
               [mkDiag Hint "unneeded identical mapping of" a]
             _ -> []
  appendDiags ws
  w <- symbToRaw k u
  x <- symbToRaw k v
  return (w, x)

statSymbItems :: [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sl =
  let check l = case l of
         Symb_id _ : Qual_id b _ _ : r ->
            mkDiag Warning "qualification in list only applies to" b : check r
         _ : r -> check r
         [] -> []
      st (Symb_items kind l _) = do
        appendDiags $ check l
        mapM (symbToRaw kind) l
  in fmap concat (mapM st sl)

symbToRaw :: SYMB_KIND -> SYMB -> Result RawSymbol
symbToRaw k si = case si of
  Symb_id idt -> return $ symbKindToRaw k idt
  Qual_id idt t _ -> typedSymbKindToRaw k idt t

symbKindToRaw :: SYMB_KIND -> Id -> RawSymbol
symbKindToRaw sk idt = case sk of
    Implicit -> AnID idt
    _ -> AKindedId (case sk of
      Sorts_kind -> SortKind
      Preds_kind -> PredKind
      _ -> FunKind) idt

typedSymbKindToRaw :: SYMB_KIND -> Id -> TYPE -> Result RawSymbol
typedSymbKindToRaw k idt t = let
     err = plain_error (AnID idt)
              (showDoc idt ":" ++ showDoc t
               "does not have kind" ++ showDoc k "") nullRange
     aSymb = ASymbol $ case t of
       O_type ot -> idToOpSymbol idt $ toOpType ot
       P_type pt -> idToPredSymbol idt $ toPredType pt
             -- in case of ambiguity, return a constant function type
             -- this deviates from the CASL summary !!!
       A_type s ->
           let ot = OpType {opKind = Total, opArgs = [], opRes = s}
           in idToOpSymbol idt ot
    in case k of
    Implicit -> return aSymb
    Sorts_kind -> err
    Ops_kind -> case t of
        P_type _ -> err
        _ -> return aSymb
    Preds_kind -> case t of
        O_type _ -> err
        A_type s -> return $ ASymbol $
                    let pt = PredType {predArgs = [s]}
                    in idToPredSymbol idt pt
        P_type _ -> return aSymb

symbMapToMorphism :: m -> Sign f e -> Sign f e
                  -> SymbolMap -> Result (Morphism f e m)
symbMapToMorphism extEm sigma1 sigma2 smap = let
  sort_map1 = Set.fold mapMSort Map.empty (sortSet sigma1)
  mapMSort s m =
    case Map.lookup (Symbol {symName = s, symbType = SortAsItemType}) smap
    of Just sym -> let t = symName sym in if s == t then m else
                           Map.insert s t m
       Nothing -> m
  fun_map1 = Map.foldWithKey mapFun Map.empty (opMap sigma1)
  pred_map1 = Map.foldWithKey mapPred Map.empty (predMap sigma1)
  mapFun i ots m = Set.fold (insFun i) m ots
  insFun i ot m =
    case Map.lookup (Symbol {symName = i, symbType = OpAsItemType ot}) smap
    of Just sym -> let j = symName sym in case symbType sym of
         OpAsItemType oty -> let k = opKind oty in
            if j == i && opKind ot == k then m
            else Map.insert (i, ot {opKind = Partial}) (j, k) m
         _ -> m
       _ -> m
  mapPred i pts m = Set.fold (insPred i) m pts
  insPred i pt m =
    case Map.lookup (Symbol {symName = i, symbType = PredAsItemType pt}) smap
    of Just sym -> let j = symName sym in  case symbType sym of
         PredAsItemType _ -> if i == j then m else Map.insert (i, pt) j m
         _ -> m
       _ -> m
  in return (embedMorphism extEm sigma1 sigma2)
     { sort_map = sort_map1
     , fun_map = fun_map1
     , pred_map = pred_map1 }

morphismToSymbMap :: Morphism f e m -> SymbolMap
morphismToSymbMap = morphismToSymbMapAux False

morphismToSymbMapAux :: Bool -> Morphism f e m -> SymbolMap
morphismToSymbMapAux b mor = let
    src = msource mor
    sorts = sort_map mor
    ops = fun_map mor
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
matches x@(Symbol idt k) rs = case rs of
    ASymbol y -> x == y
    AnID di -> idt == di
    AKindedId rk di -> let res = idt == di in case (k, rk) of
        (SortAsItemType, SortKind) -> res
        (OpAsItemType _, FunKind) -> res
        (PredAsItemType _, PredKind) -> res
        _ -> False

idMor :: m -> Sign f e -> Morphism f e m
idMor extEm sigma = (embedMorphism extEm sigma sigma) { morKind = IdMor }

compose :: (Eq e, Eq f) => (m -> m -> m)
        -> Morphism f e m -> Morphism f e m -> Result (Morphism f e m)
compose comp mor1 mor2 = if mtarget mor1 == msource mor2 then
  let sMap1 = sort_map mor1
      src = msource mor1
      tar = mtarget mor2
      fMap1 = fun_map mor1
      pMap1 = pred_map mor1
      sMap2 = sort_map mor2
      fMap2 = fun_map mor2
      pMap2 = pred_map mor2
      sMap = if Map.null sMap2 then sMap1 else
             Set.fold ( \ i ->
                       let j = mapSort sMap2 (mapSort sMap1 i) in
                       if i == j then id else Map.insert i j)
                 Map.empty $ sortSet src
      emb = (embedMorphism (comp (extended_map mor1) $ extended_map mor2)
             src tar) { morKind = max (morKind mor1) $ morKind mor2 }
  in return $
     if Map.null sMap1 &&  Map.null sMap2 && Map.null fMap1 && Map.null fMap2
        && Map.null pMap1 && Map.null pMap2 then emb else emb
     { sort_map = sMap
     , fun_map  = if Map.null fMap2 then fMap1 else
                 Map.foldWithKey ( \ i t m ->
                   Set.fold ( \ ot ->
                       let (ni, nt) = mapOpSym sMap2 fMap2 $
                                      mapOpSym sMap1 fMap1 (i, ot)
                           k = opKind nt
                       in assert (mapOpTypeK sMap k ot == nt) $
                          if i == ni && opKind ot == k then id else
                          Map.insert (i, ot {opKind = Partial }) (ni, k)) m t)
                     Map.empty $ opMap src
     , pred_map = if Map.null pMap2 then pMap1 else
                 Map.foldWithKey ( \ i t m ->
                   Set.fold ( \ pt ->
                       let (ni, nt) = mapPredSym sMap2 pMap2 $
                                     mapPredSym sMap1 pMap1 (i, pt)
                       in assert (mapPredType sMap pt == nt) $
                       if i == ni then id else Map.insert (i, pt) ni) m t)
                      Map.empty $ predMap src }
    else fail "target of first and source of second morphism are different"

legalSign :: Sign f e -> Bool
legalSign sigma =
  Map.foldWithKey (\s sset b -> b && legalSort s && all legalSort
                                (Set.toList sset))
                  True (Rel.toMap (sortRel sigma))
  && Map.fold (\ts b -> b && all legalOpType (Set.toList ts))
              True (opMap sigma)
  && Map.fold (\ts b -> b && all legalPredType (Set.toList ts))
              True (predMap sigma)
  where sorts = sortSet sigma
        legalSort s = Set.member s sorts
        legalOpType t = legalSort (opRes t)
                        && all legalSort (opArgs t)
        legalPredType t = all legalSort (predArgs t)

inducedOpMap :: Sort_map -> Fun_map -> OpMap -> OpMap
inducedOpMap sm fm os = Map.foldWithKey
  ( \ i -> flip $ Set.fold ( \ ot ->
      let (j, nt) = mapOpSym sm fm (i, ot)
      in Rel.setInsert j nt)) Map.empty os

inducedPredMap :: Sort_map -> Pred_map -> Map.Map Id (Set.Set PredType)
               -> Map.Map Id (Set.Set PredType)
inducedPredMap sm pm ps = Map.foldWithKey
  ( \ i -> flip $ Set.fold ( \ ot ->
      let (j, nt) = mapPredSym sm pm (i, ot)
      in Rel.setInsert j nt)) Map.empty ps

legalMor :: Morphism f e m -> Bool
legalMor mor =
  let s1 = msource mor
      s2 = mtarget mor
      sm = sort_map mor
      msorts = Set.map $ mapSort sm
  in legalSign s1
  && Set.isSubsetOf (msorts $ sortSet s1) (sortSet s2)
  && Set.isSubsetOf (msorts $ emptySortSet s1) (emptySortSet s2)
  && isSubOpMap (inducedOpMap sm (fun_map mor) $ opMap s1) (opMap s2)
  && isSubMapSet (inducedPredMap sm (pred_map mor) $ predMap s1) (predMap s2)
  && legalSign s2

idOrInclMorphism :: (e -> e -> Bool) -> Morphism f e m -> Morphism f e m
idOrInclMorphism isSubExt m =
  let src = msource m
      tar = mtarget m
  in if isSubSig isSubExt tar src then m { morKind = IdMor }
     else let diffOpMap = diffMapSet (opMap src) $ opMap tar in
          m { morKind = InclMor
            , fun_map = Map.fromList $ concatMap (\ (i, s) ->
              map (\ t -> ((i, t), (i, Total)))
                 $ Set.toList s) $ Map.toList diffOpMap }

sigInclusion :: (Pretty f, Pretty e)
             => m -- ^ compute extended morphism
             -> (e -> e -> Bool) -- ^ subsignature test of extensions
             -> (e -> e -> e) -- ^ difference of signature extensions
             -> Sign f e -> Sign f e -> Result (Morphism f e m)
sigInclusion extEm isSubExt diffExt sigma1 sigma2 =
  if isSubSig isSubExt sigma1 sigma2 then
     return $ idOrInclMorphism isSubExt $ embedMorphism extEm sigma1 sigma2
  else Result [Diag Error
          ("Attempt to construct inclusion between non-subsignatures:\n"
           ++ showDoc (diffSig diffExt sigma1 sigma2) "") nullRange] Nothing

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
      omap1 = fun_map mor1
      omap2 = fun_map mor2
      uo1 = foldr delOp (opMap s1) $ Map.keys omap1
      uo2 = foldr delOp (opMap s2) $ Map.keys omap2
      delOp (n, ot) m = diffMapSet m $ Map.singleton n $
                    Set.fromList [ot {opKind = Partial}, ot {opKind = Total}]
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
              ( \ (a, s) -> map ( \ ot -> ((a, ot {opKind = Partial}),
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
    let o3 = opMap s3
    return
      (embedMorphism (uniteM (extended_map mor1) $ extended_map mor2) s3 s4)
      { morKind = max (morKind mor1) $ morKind mor2
      , sort_map = Map.filterWithKey (/=) smap
      , fun_map = Map.filterWithKey
        (\ (i, ot) (j, k) -> i /= j || k == Total && Set.member ot
         (Map.findWithDefault Set.empty i o3)) omap
      , pred_map = Map.filterWithKey (\ (i, _) j -> i /= j) pmap }
    else Result pds Nothing

isSortInjective :: Morphism f e m -> Bool
isSortInjective m =
   null [() | k1 <- src, k2 <- src, k1 /= k2,
              (Map.lookup k1 sm :: Maybe SORT) == Map.lookup k2 sm]
   where sm = sort_map m
         src = Map.keys sm

isInjective :: Morphism f e m -> Bool
isInjective m =
   null [() | k1 <- src, k2 <- src, k1 /= k2,
              (Map.lookup k1 symmap :: Maybe Symbol) == Map.lookup k2 symmap]
   where src = Map.keys symmap
         symmap = morphismToSymbMap m

instance Pretty Kind where
  pretty k = keyword $ case k of
      SortKind -> sortS
      FunKind -> opS
      PredKind -> predS

instance Pretty RawSymbol where
  pretty rsym = case rsym of
    ASymbol sy -> pretty sy
    AnID i -> pretty i
    AKindedId k i -> pretty k <+> pretty i

printMorphism :: (f -> Doc) -> (e -> Doc) -> (m -> Doc) -> Morphism f e m
              -> Doc
printMorphism fF fE fM mor =
    let src = msource mor
        tar = mtarget mor
        ops = fun_map mor
        prSig s = specBraces (space <> printSign fF fE s)
        srcD = prSig src
    in case morKind mor of
    IdMor -> fsep [text "identity morphism over", srcD]
    InclMor -> fsep
      [ text "inclusion morphism of", srcD
      , fsep $ if Map.null ops then
          [ text "extended with"
          , pretty $ Set.difference (symOf tar) $ symOf src ]
        else
          [ text "by totalizing"
          , pretty $ Set.map (uncurry idToOpSymbol) $ Map.keysSet ops ]]
    OtherMor -> fsep
      [ pretty (morphismToSymbMapAux True mor)
          $+$ fM (extended_map mor)
      , colon <+> srcD, mapsto <+> prSig tar ]

instance (Pretty e, Pretty f, Pretty m) =>
    Pretty (Morphism f e m) where
       pretty = printMorphism pretty pretty pretty

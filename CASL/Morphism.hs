
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Till Mossakowski and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
Symbols and signature morphisms for the CASL logic
-}

{-
todo:
issue warning for symbols lists like __ * __, __ + __: Elem * Elem -> Elem
the qualification only applies to __+__ !
-}

module CASL.Morphism where

import CASL.StaticAna
import CASL.Sign
import CASL.AS_Basic_CASL
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Data.Dynamic
import Control.Monad
import Common.PrettyPrint
import Common.Lib.Pretty

data SymbType = OpAsItemType OpType
                -- since symbols do not speak about totality, the totality
                -- information in OpType has to be ignored
	      | PredAsItemType PredType
	      | SortAsItemType 
		deriving (Show)
-- Ordering and equality of symbol types has to ingore totality information
instance Ord SymbType where
  compare (OpAsItemType ot1) (OpAsItemType ot2) =
    compare (opArgs ot1,opRes ot1) (opArgs ot2,opRes ot2)
  compare (OpAsItemType _)  _ = LT
  compare (PredAsItemType pt1) (PredAsItemType pt2) =
    compare pt1 pt2
  compare (PredAsItemType _) (OpAsItemType _) = GT
  compare (PredAsItemType _) SortAsItemType = LT
  compare SortAsItemType SortAsItemType  = EQ
  compare SortAsItemType _  = GT

instance Eq SymbType where
  t1 == t2 = compare t1 t2 == EQ

data Symbol = Symbol {symName :: Id, symbType :: SymbType} 
	      deriving (Show, Eq, Ord)

type SymbolSet = Set.Set Symbol 
type SymbolMap = Map.EndoMap Symbol 

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
    	         deriving (Show, Eq, Ord)

type RawSymbolSet = Set.Set RawSymbol 
type RawSymbolMap = Map.EndoMap RawSymbol 

data Kind = SortKind | FunKind | PredKind
            deriving (Show, Eq, Ord)

type Sort_map = Map.Map SORT SORT
type Fun_map =  Map.Map (Id,OpType) (Id, FunKind)
type Pred_map = Map.Map (Id,PredType) Id

data Morphism = Morphism {msource :: Sign,
			  mtarget :: Sign,
                          sort_map :: Sort_map, 
                          fun_map :: Fun_map, 
                          pred_map :: Pred_map}
                         deriving (Eq, Show)

mapSort :: Sort_map -> SORT -> SORT
mapSort sorts s = Map.findWithDefault s s sorts

mapOpType :: Sort_map -> OpType -> OpType
mapOpType sorts t = t { opArgs = map (mapSort sorts) $ opArgs t
		      , opRes = mapSort sorts $ opRes t }

mapOpTypeK :: Sort_map -> FunKind -> OpType -> OpType
mapOpTypeK sorts k t = makeTotal k $ mapOpType sorts t

makeTotal :: FunKind -> OpType -> OpType
makeTotal Total t = t { opKind = Total }
makeTotal _ t = t

mapOpSym :: Sort_map -> Fun_map -> (Id,OpType) -> Maybe (Id,OpType)
mapOpSym sMap fMap (id,ot) = do
  (id',k) <- Map.lookup (id,ot) fMap
  return (id',mapOpTypeK sMap k ot)

-- | Check if two OpTypes are equal except from totality or partiality
compatibleOpTypes :: OpType -> OpType -> Bool
compatibleOpTypes ot1 ot2 = opArgs ot1 == opArgs ot2 && opRes ot1 == opRes ot2

mapPredType :: Sort_map -> PredType -> PredType
mapPredType sorts t = t { predArgs = map (mapSort sorts) $ predArgs t }

mapPredSym :: Sort_map -> Pred_map -> (Id,PredType) -> Maybe (Id,PredType)
mapPredSym sMap fMap (id,pt) = do
  id' <- Map.lookup (id,pt) fMap
  return (id',mapPredType sMap pt)

embedMorphism :: Sign -> Sign -> Morphism
embedMorphism a b =
    Morphism 
    { msource = a 
    , mtarget = b
    , sort_map = Set.fold (\x -> Map.insert x x) Map.empty
                  $ sortSet a 
    , fun_map = Map.foldWithKey 
                 ( \ i ts m -> Set.fold 
                      (\t -> Map.insert (i,t) (i, opKind t)) m ts)
                 Map.empty
                 (opMap a)
    , pred_map = Map.foldWithKey 
                 ( \ i ts m -> Set.fold 
                      (\t -> Map.insert (i,t) i) m ts)
                 Map.empty
                 (predMap a)
    }

-- Typeable instance
sentenceTc, signTc, morphismTc, symbolTc, rawSymbolTc 
    :: TyCon
sentenceTc       = mkTyCon "CASL.Morphism.FORMULA"
signTc           = mkTyCon "CASL.Morphism.Sign"
morphismTc       = mkTyCon "CASL.Morphism.Morphism"
symbolTc         = mkTyCon "CASL.Morphism.Symbol"
rawSymbolTc      = mkTyCon "CASL.Morphism.RawSymbol"

instance Typeable FORMULA where
  typeOf _ = mkAppTy sentenceTc []
instance Typeable Sign where
  typeOf _ = mkAppTy signTc []
instance Typeable Morphism where
  typeOf _ = mkAppTy morphismTc []
instance Typeable Symbol where
  typeOf _ = mkAppTy symbolTc []
instance Typeable RawSymbol where
  typeOf _ = mkAppTy rawSymbolTc []


idToSortSymbol :: Id -> Symbol
idToSortSymbol idt = Symbol idt SortAsItemType

idToOpSymbol :: Id -> OpType -> Symbol
idToOpSymbol idt typ = Symbol idt (OpAsItemType typ)

idToPredSymbol :: Id -> PredType -> Symbol
idToPredSymbol idt typ = Symbol idt (PredAsItemType typ)

symbTypeToKind :: SymbType -> Kind
symbTypeToKind (OpAsItemType _) = FunKind
symbTypeToKind (PredAsItemType _)     = PredKind
symbTypeToKind SortAsItemType      = SortKind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw sym = ASymbol sym

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> SORT
rawSymName (ASymbol sym) = symName sym
rawSymName (AnID id) = id
rawSymName (AKindedId _ id) = id

symOf :: Sign -> SymbolSet
symOf sigma = 
    let sorts = Set.image idToSortSymbol $ sortSet sigma
	ops = Set.fromList $ 
	      concatMap (\ (i, ts) -> map ( \ t -> idToOpSymbol i t) 
			 $ Set.toList ts) $ 
	      Map.toList $ opMap sigma
	preds = Set.fromList $ 
	      concatMap (\ (i, ts) -> map ( \ t -> idToPredSymbol i t) 
			 $ Set.toList ts) $ 
	      Map.toList $ predMap sigma
	in Set.unions [sorts, ops, preds] 

statSymbMapItems :: [SYMB_MAP_ITEMS] -> Result RawSymbolMap
statSymbMapItems sl = do
  ls <- sequence $ map s1 sl
  foldl insertRsys (return Map.empty) (concat ls)
  where
  s1 (Symb_map_items kind l _) = sequence (map (symbOrMapToRaw kind) l)
  insertRsys m (rsy1,rsy2) = do
    m1 <- m
    case Map.lookup rsy1 m1 of
      Nothing -> return $ Map.insert rsy1 rsy2 m1
      Just rsy3 -> 
        plain_error m1 ("Symbol "++showPretty rsy1 " mapped twice to "
                ++showPretty rsy2 " and "++showPretty rsy3 "") nullPos

pairM :: Monad m => (m a,m b) -> m (a,b)
pairM (x,y) = do
  a <- x
  b <- y
  return (a,b)

symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> Result (RawSymbol,RawSymbol)
symbOrMapToRaw k (Symb s) = pairM (symbToRaw k s,symbToRaw k s)
symbOrMapToRaw k (Symb_map s t _) = pairM (symbToRaw k s,symbToRaw k t)

statSymbItems :: [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sl = 
  fmap concat (sequence (map s1 sl))
  where s1 (Symb_items kind l _) = sequence (map (symbToRaw kind) l)

symbToRaw :: SYMB_KIND -> SYMB -> Result RawSymbol
symbToRaw k (Symb_id idt)     = symbKindToRaw k idt
symbToRaw k (Qual_id idt t _) = typedSymbKindToRaw k idt t

symbKindToRaw :: SYMB_KIND -> Id -> Result RawSymbol
symbKindToRaw Implicit     idt = return (AnID idt)
symbKindToRaw (Sorts_kind) idt = return (AKindedId SortKind idt)
symbKindToRaw (Ops_kind)   idt = return (AKindedId FunKind  idt)
symbKindToRaw (Preds_kind) idt = return (AKindedId PredKind idt)

typedSymbKindToRaw :: SYMB_KIND -> Id -> TYPE -> Result RawSymbol
typedSymbKindToRaw Implicit   idt (O_type ot) = 
  return (ASymbol (idToOpSymbol idt (toOpType ot)))
typedSymbKindToRaw Implicit   idt (P_type pt) = 
  return (ASymbol (idToPredSymbol idt (toPredType pt)))
-- in case of ambiguity, return a constant function type
-- this deviates from the CASL summary !!!
typedSymbKindToRaw Implicit   idt (A_type s) = 
  return (ASymbol (idToOpSymbol idt ot))
  where ot = OpType {opKind = Total, opArgs = [], opRes = s}
typedSymbKindToRaw (Sorts_kind) idt _ = return (AKindedId SortKind idt)
typedSymbKindToRaw (Ops_kind)   idt (O_type ot) = 
  return (ASymbol (idToOpSymbol idt (toOpType ot)))
typedSymbKindToRaw (Preds_kind)   idt (P_type pt) = 
  return (ASymbol (idToPredSymbol idt (toPredType pt)))
typedSymbKindToRaw (Ops_kind)   idt (A_type s) = 
  return (ASymbol (idToOpSymbol idt ot))
  where ot = OpType {opKind = Total, opArgs = [], opRes = s}
typedSymbKindToRaw (Preds_kind)   idt (A_type s) = 
  return (ASymbol (idToPredSymbol idt pt))
  where pt = PredType {predArgs = [s]}
typedSymbKindToRaw k idt t = 
  plain_error (AnID idt) 
     (showPretty idt ":" ++ showPretty t 
      "does not have kind" ++showPretty k "") nullPos

symbMapToMorphism :: Sign -> Sign -> SymbolMap -> Result Morphism
symbMapToMorphism sigma1 sigma2 smap = do
  sort_map1 <- Set.fold mapSort (return Map.empty) (sortSet sigma1)
  fun_map1 <- Map.foldWithKey mapFun (return Map.empty)  (opMap sigma1)
  pred_map1 <- Map.foldWithKey mapPred (return Map.empty) (predMap sigma1)
  return (Morphism { msource = sigma1,
             mtarget = sigma2,
             sort_map = sort_map1,
             fun_map = fun_map1,
             pred_map = pred_map1})
  where
  mapSort s m = do
    m1 <- m 
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map sort "++showPretty s "")
             $ Map.lookup (Symbol {symName = s, symbType = SortAsItemType}) smap
    return (Map.insert s (symName sym) m1)
  mapFun id ots m = Set.fold (insFun id) m ots
  insFun id ot m = do
    m1 <- m
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map op "++showPretty id "")
             $ Map.lookup (Symbol {symName = id, symbType = OpAsItemType ot}) smap
    k <- case symbType sym of
        OpAsItemType ot -> return $ opKind ot
        _ -> plain_error Total
              ("symbMapToMorphism - Wrong result symbol type for op"
               ++showPretty id "") nullPos 
    return (Map.insert (id,ot) (symName sym,k) m1)
  mapPred id pts m = Set.fold (insPred id) m pts
  insPred id pt m = do
    m1 <- m
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map pred "++showPretty id "")
             $ Map.lookup (Symbol {symName = id, symbType = PredAsItemType pt}) 
               smap
    case symbType sym of
        PredAsItemType ot -> return ()
        _ -> plain_error ()
              ("symbMapToMorphism - Wrong result symbol type for pred"
               ++showPretty id "") nullPos 
    return (Map.insert (id,pt) (symName sym) m1)
      
morphismToSymbMap :: Morphism -> SymbolMap
morphismToSymbMap (Morphism src _ sorts ops preds) =
  let
    sortSymMap = 
      Map.foldWithKey
         ( \ s1 s2 -> Map.insert (idToSortSymbol s1) (idToSortSymbol s2))
         Map.empty
         sorts
    opSymMap = 
      Map.foldWithKey
         ( \ (id1,t) (id2,k) -> 
             Map.insert (idToOpSymbol id1 t) 
                        (idToOpSymbol id2 $ mapOpTypeK sorts k t))
         Map.empty
         ops
    predSymMap = 
      Map.foldWithKey
         ( \ (id1,t) id2 -> 
             Map.insert (idToPredSymbol id1 t) 
                        (idToPredSymbol id2 $ mapPredType sorts t))
         Map.empty
         preds
  in
    foldr Map.union sortSymMap [opSymMap,predSymMap]


matches :: Symbol -> RawSymbol -> Bool
matches x                            (ASymbol y)              =  x==y
matches (Symbol idt _)                (AnID di)               = idt==di
matches (Symbol idt SortAsItemType)        (AKindedId SortKind di) = idt==di
matches (Symbol idt (OpAsItemType _)) (AKindedId FunKind di)  = idt==di
matches (Symbol idt (PredAsItemType _))     (AKindedId PredKind di) = idt==di
matches _                            _                        = False


idMor :: Sign -> Morphism
idMor sigma =
  Morphism { 
    msource = sigma,
    mtarget = sigma,
    sort_map = Set.fold (\s -> Map.insert s s) Map.empty (sortSet sigma),
    fun_map =
      Map.foldWithKey 
        (\id ts m -> Set.fold (\t -> Map.insert (id,t) (id,opKind t)) m ts) 
        Map.empty (opMap sigma),
    pred_map = 
      Map.foldWithKey
        (\id ts m -> Set.fold (\t -> Map.insert (id,t) id) m ts) 
        Map.empty (predMap sigma)
            }

compose :: Morphism -> Morphism -> Maybe Morphism
compose mor1 mor2 = 
  if mtarget mor1 == msource mor2 
    then Just $ Morphism {
      msource = msource mor1,
      mtarget = mtarget mor2,
      sort_map = Map.map (mapSort (sort_map mor2)) (sort_map mor1),
      fun_map = Map.mapWithKey mapOpId (fun_map mor1),
      pred_map = Map.mapWithKey mapPredId (pred_map mor1)
      }
    else Nothing
  where
  mapOpId :: (Id, OpType) -> (Id,FunKind) -> (Id,FunKind)
  mapOpId (id,t) (id1,k1) =
    Map.find (id1,mapOpType (sort_map mor1) t) (fun_map mor2)
  mapPredId :: (Id, PredType) -> Id -> Id
  mapPredId (id,t) id1 =
    Map.find (id1,mapPredType (sort_map mor1) t) (pred_map mor2)
  -- ??? dangerous use of Map.find here (may lead to call of error!)


legalSign sigma =
  Map.foldWithKey (\s sset b -> b && legalSort s && Set.all legalSort sset)
                  True (Rel.toMap (sortRel sigma))
  && Map.fold (\ts b -> b && Set.all legalOpType ts) 
              True (opMap sigma)
  && Map.fold (\ts b -> b && Set.all legalPredType ts) 
              True (predMap sigma)
  && Map.fold (\sset b -> b && Set.all legalSort sset) 
              True (varMap sigma)
  where sorts = sortSet sigma
        legalSort s = Set.member s sorts
        legalOpType t = legalSort (opRes t) 
                        && all legalSort (opArgs t) 
        legalPredType t = all legalSort (predArgs t) 

legalMor mor =
  legalSign sigma1
  && legalSign sigma2
  && Map.foldWithKey
        (\s1 s2 b -> b && Set.member s1 (sortSet sigma1)
                       && Set.member s2 (sortSet sigma2))
        True smap
  && Map.foldWithKey 
        (\(id1,t) (id2,k) b -> 
           b
           &&
           Set.member t (Map.findWithDefault Set.empty id1 (opMap sigma1)) 
           &&
           Set.member (mapOpTypeK smap k t) 
                      (Map.findWithDefault Set.empty id2 (opMap sigma2))
        )
        True (fun_map mor)
  && Map.foldWithKey 
        (\(id1,t) id2 b -> 
           b
           &&
           Set.member t (Map.findWithDefault Set.empty id1 (predMap sigma1)) 
           &&
           Set.member (mapPredType smap t) 
                      (Map.findWithDefault Set.empty id2 (predMap sigma2))
        )
        True (pred_map mor)
  where sigma1 = msource mor
        sigma2 = mtarget mor
        smap = sort_map mor

sigInclusion :: Sign -> Sign -> Result Morphism
sigInclusion sigma1 sigma2 = 
  if isSubSig sigma1 sigma2 
     then return (embedMorphism sigma1 sigma2)
     else pplain_error (embedMorphism emptySign emptySign)
          (ptext "Attempt to construct inclusion between non-subsignatures:"
           $$ ptext "Singature 1:" $$ printText sigma1
           $$ ptext "Singature 2:" $$ printText sigma2)
           nullPos

morphismUnion mor1 mor2 = do
  let src = msource mor1 `addSig` msource mor2
      tar = mtarget mor1 `addSig` mtarget mor2
      smap = sort_map mor1 `Map.union` sort_map mor2
      fmap = fun_map mor1 `Map.union` fun_map mor2
      pmap = pred_map mor1 `Map.union` pred_map mor2
  when (not (sort_map mor2 `Map.subset` smap))
    (pplain_error () 
      (ptext "Incompatible signature morphisms."
        $$ ptext "The following sorts are mapped differently"
        <+> printText (Set.fromList
               (sort_map mor1 `Map.differentKeys` sort_map mor2)))
      nullPos)
  when (not (fun_map mor2 `Map.subset` fmap))
    (pplain_error () 
      (ptext "Incompatible signature morphisms."
        $$ ptext "The following operations are mapped differently"
        <+> printText (Set.fromList
              (map (\(id,ot) -> idToOpSymbol id ot)
                (fun_map mor1 `Map.differentKeys` fun_map mor2))))
      nullPos)
  when (not (pred_map mor2 `Map.subset` pmap))
    (pplain_error () 
      (ptext "Incompatible signature morphisms."
        $$ ptext "The following predicates are mapped differently"
        <+> printText (Set.fromList
              (map (\(id,pt) -> idToPredSymbol id pt)
                (pred_map mor1 `Map.differentKeys` pred_map mor2))))
      nullPos)
  return $ Morphism { msource = src,
                      mtarget = tar,
                      sort_map = smap, 
                      fun_map = fmap, 
                      pred_map = pmap }

instance PrettyPrint Symbol where
  printText0 ga sy = 
    printText0 ga (symName sy) <> 
    (if isEmpty t then empty
      else ptext ":" <> t)
    where
    t = printText0 ga (symbType sy)

instance PrettyPrint SymbType where
  printText0 ga (OpAsItemType ot) = printText0 ga ot
  printText0 ga	(PredAsItemType pt) = printText0 ga pt
  printText0 ga	SortAsItemType = empty 

instance PrettyPrint Kind where
  printText0 _ SortKind = ptext "sort"
  printText0 _ FunKind = ptext "op"
  printText0 _ PredKind = ptext "pred"


instance PrettyPrint RawSymbol where
  printText0 ga rsym = case rsym of
    ASymbol sy -> printText0 ga sy
    AnID id -> printText0 ga id
    AKindedId k id -> printText0 ga k <+> printText0 ga id


instance PrettyPrint Morphism where
  printText0 ga mor = 
   (if null sorts then empty
       else ptext "sorts" <+> (fsep $ punctuate comma sorts))
   $$ 
   (if null ops then empty
       else ptext "ops" <+> (fsep $ punctuate comma ops))
   $$
   (if null preds then empty
       else ptext "preds" <+> (fsep $ punctuate comma preds))
   <+>
   ptext " : " $$ 
   ptext "{" <+>  printText0 ga (msource mor) <+> ptext "}" <+> 
   ptext "->" <+> 
   ptext "{" <+>  printText0 ga (mtarget mor) <+> ptext "}"
   where sorts = map print_sort_map (Map.toList $ sort_map mor)
         print_sort_map (s1,s2) = 
           printText0 ga s1 <+> ptext "|->" <+> printText0 ga s2
         ops = map print_op_map (Map.toList $ fun_map mor)
         print_op_map ((id1,ot),(id2,kind)) = 
           printText0 ga (Qual_op_name id1 (toOP_TYPE ot) [])
           <+> ptext "|->" <+> 
           printText0 ga id2
         preds = map print_pred_map (Map.toList $ pred_map mor)
         print_pred_map ((id1,pt),id2) = 
           printText0 ga (Qual_pred_name id1 (toPRED_TYPE pt) [])
           <+> ptext "|->" <+> 
           printText0 ga id2

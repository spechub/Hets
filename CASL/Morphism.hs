
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
the symbol and morphism stuff for a logic

-}

module CASL.Morphism where

import CASL.StaticAna
import CASL.AS_Basic_CASL
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Data.Dynamic
import Common.PrettyPrint
import Common.Lib.Pretty

data SymbType = OpAsItemType OpType
	      | PredAsItemType PredType
	      | SortAsItemType 
		deriving (Show, Eq, Ord)

data Symbol = Symbol {symName :: Id, symbType :: SymbType} 
	      deriving (Show, Eq, Ord)

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
    	         deriving (Show, Eq, Ord)

data Kind = SortKind | FunKind | PredKind
            deriving (Show, Eq, Ord)

type Sort_map = Map.Map SORT SORT
type Fun_map =  Map.Map (Id,OpType) (Id, FunKind)
type Pred_map = Map.Map (Id,PredType) Id

data Morphism = Morphism {msource,mtarget :: Sign,
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

mapPredType :: Sort_map -> PredType -> PredType
mapPredType sorts t = t { predArgs = map (mapSort sorts) $ predArgs t }

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
sentenceTc       = mkTyCon "CASL.Morphism.Sentence"
signTc           = mkTyCon "CASL.Morphism.Sign"
morphismTc       = mkTyCon "CASL.Morphism.Morphism"
symbolTc         = mkTyCon "CASL.Morphism.Symbol"
rawSymbolTc      = mkTyCon "CASL.Morphism.RawSymbol"

instance Typeable Sentence where
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
symbolToRaw (Symbol idt typ) = AKindedId (symbTypeToKind typ) idt

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> SORT
rawSymName (ASymbol sym) = symName sym
rawSymName (AnID id) = id
rawSymName (AKindedId _ id) = id

symOf :: Sign -> Set.Set Symbol
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

statSymbMapItems :: [SYMB_MAP_ITEMS] -> Result (Map.Map RawSymbol RawSymbol)
statSymbMapItems sl =  return (Map.fromList $ concat $ map s1 sl)
  where
  s1 (Symb_map_items kind l _) = map (symbOrMapToRaw kind) l
 
symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> (RawSymbol,RawSymbol)
symbOrMapToRaw k (Symb s) = (symbToRaw k s,symbToRaw k s)
symbOrMapToRaw k (Symb_map s t _) = (symbToRaw k s,symbToRaw k t)

statSymbItems :: [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sl = 
  return (concat (map s1 sl))
  where s1 (Symb_items kind l _) = map (symbToRaw kind) l

symbToRaw :: SYMB_KIND -> SYMB -> RawSymbol
symbToRaw k (Symb_id idt)     = symbKindToRaw k idt
symbToRaw k (Qual_id idt _ _) = symbKindToRaw k idt

symbKindToRaw :: SYMB_KIND -> Id -> RawSymbol
symbKindToRaw Implicit     idt = AnID idt
symbKindToRaw (Sorts_kind) idt = AKindedId SortKind idt
symbKindToRaw (Ops_kind)   idt = AKindedId FunKind  idt
symbKindToRaw (Preds_kind) idt = AKindedId PredKind idt

symmapOf :: Morphism -> Map.Map Symbol Symbol
symmapOf (Morphism src _ sorts ops preds) =
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


instance PrettyPrint Morphism where
  printText0 ga mor = 
   (if null sorts then empty
       else ptext "sorts" <+> (fsep $ punctuate comma sorts))
   <+> 
   (if null ops then empty
       else ptext "ops" <+> (fsep $ punctuate comma ops))
   <+>
   (if null preds then empty
       else ptext "preds" <+> (fsep $ punctuate comma preds))
   <+>
   ptext " : " <+> 
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

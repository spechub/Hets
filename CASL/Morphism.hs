
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

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
import Data.Dynamic

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
type Fun_map =  Map.Map Id (Set.Set (OpType, Id, FunKind)) 
type Pred_map = Map.Map Id (Set.Set (PredType, Id))

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
    , sort_map = Map.fromList $ map (\x -> (x,x)) $
      Set.toList $ sortSet a 
    , fun_map = Map.mapWithKey ( \ i -> Set.fromList . map 
				 ( \ e -> (e, i, opKind e)) 
				 . Set.toList) $ opMap a 
    , pred_map = Map.mapWithKey ( \ i -> Set.fromList . map 
				 ( \ e -> (e, i)) 
				 . Set.toList) $ predMap a 
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

symOf :: Sign -> Set.Set Symbol
symOf sigma = 
    let sorts = Set.fromList $ map idToSortSymbol
		$ Set.toList $ sortSet sigma
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
    sortSymMap = Map.fromList $ map 
		 ( \ (a, b) -> (idToSortSymbol a, idToSortSymbol b))
		 $ Map.toList sorts
    opSymMap = Map.fromList $ concatMap 
        ( \ (i, t :: Set.Set (OpType, Id, FunKind)) -> 
	      concatMap 
	          ( \ o -> 
		    let ot = mapOpType sorts o
		    in map ( \ (_, j, k) -> 
			     (idToOpSymbol i o, idToOpSymbol j 
			                        $ makeTotal k ot))
			    $ Set.toList $ Set.filter 
		           ( \ (ty, _ , _) -> 
			     makeTotal Total ty == makeTotal Total ot) t)
	      $ Set.toList $ Map.findWithDefault Set.empty i $ opMap src)
	$ Map.toList ops 
    predSymMap = Map.fromList $ concatMap 
        ( \ (i, t :: Set.Set (PredType, Id)) -> 
	      concatMap 
	          ( \ p -> 
		    let pt = mapPredType sorts p
		    in map ( \ (_, j) -> 
			     (idToPredSymbol i p, idToPredSymbol j pt))
			    $ Set.toList $ Set.filter ((==pt) . fst) t)
	      $ Set.toList $ Map.findWithDefault Set.empty i $ predMap src)
	$ Map.toList preds 
  in
    foldr Map.union sortSymMap [opSymMap,predSymMap]

matches :: Symbol -> RawSymbol -> Bool
matches x                            (ASymbol y)              =  x==y
matches (Symbol idt _)                (AnID di)               = idt==di
matches (Symbol idt SortAsItemType)        (AKindedId SortKind di) = idt==di
matches (Symbol idt (OpAsItemType _)) (AKindedId FunKind di)  = idt==di
matches (Symbol idt (PredAsItemType _))     (AKindedId PredKind di) = idt==di
matches _                            _                        = False

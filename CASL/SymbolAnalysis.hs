{- |
Module      :  $Header$
Copyright   :  (c) Carsten Fischer and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
further functions for Logic instance 

-}

module CASL.SymbolAnalysis where

import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL
import CASL.Sign
import Common.Result
import CASL.Static

------------------------------------------------------------------------------
--
--                             Static Analysis
--                         Signature computations
--
------------------------------------------------------------------------------

checkItem :: Sign -> (Id,SigItem) -> Bool
checkItem sigma (idt,si) =
  let
    res   = Map.lookup idt $ getMap sigma
    items = if (isJust res) then
              fromJust res
            else
              []
  in
    si `elem` items

unfoldSigItems :: (Id, [SigItem]) -> [(Id, SigItem)]
unfoldSigItems (_,[])    = []
unfoldSigItems (idt,h:t) = (idt,h):(unfoldSigItems (idt,t))

isSubSig :: Sign -> Sign -> Bool
isSubSig sub super =
  and $ map (checkItem super) $ concat $ map unfoldSigItems
      $ Map.toList $ getMap sub

------------------------------------------------------------------------------
--
--                             Static Analysis
--                             Symbol functions
--
------------------------------------------------------------------------------

symbTypeToKind :: SymbType -> Kind
symbTypeToKind (OpAsItemType _) = FunKind
symbTypeToKind (PredType _)     = PredKind
symbTypeToKind (CASL.Sign.Sort)      = SortKind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw (Symbol idt typ) = AKindedId (symbTypeToKind typ) idt

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

sigItemToSymbol :: SigItem -> Symbol
sigItemToSymbol (ASortItem s) = Symbol (sortId $ item s) CASL.Sign.Sort
sigItemToSymbol (AnOpItem  o) = Symbol (opId $ item o)
                                       (OpAsItemType (opType $ item o))
sigItemToSymbol (APredItem p) = Symbol (predId $ item p)
                                       (PredType (predType $ item p))
				       
symOf :: Sign -> Set.Set Symbol
symOf sigma = Set.fromList $ map sigItemToSymbol 
	      $ concat $ Map.elems $ getMap sigma

funMapEntryToSymbol :: Sign -> (Id,[(OpType,Id,Bool)]) -> [(Symbol,Symbol)]
funMapEntryToSymbol _ (_,[]) = []
funMapEntryToSymbol sigma (idt,(typ,newId,_):t) =
  let
    origType = opType $ item $ getOp sigma idt
  in
    (idToOpSymbol idt origType,idToOpSymbol newId typ):
    (funMapEntryToSymbol sigma (idt,t)) 

predMapEntryToSymbol :: Sign -> (Id,[(PredType,Id)]) -> [(Symbol,Symbol)]
predMapEntryToSymbol _ (_,[]) = []
predMapEntryToSymbol sigma (idt,(typ,newId):t) =
  let
    origType = predType $ item $ getPred sigma idt
  in
    (idToPredSymbol idt origType,idToPredSymbol newId typ):
    (predMapEntryToSymbol sigma (idt,t))

symmapOf :: Morphism -> Map.Map Symbol Symbol
symmapOf (Morphism src _ sorts funs preds) =
  let
    sortMap = Map.fromList $ zip (map idToSortSymbol $ Map.keys sorts)
                             (map idToSortSymbol $ Map.elems sorts)
    funMap  = Map.fromList $ concat $ map (funMapEntryToSymbol src)
                                      (Map.toList funs)
    predMap = Map.fromList $ concat $ map (predMapEntryToSymbol src)
                                      (Map.toList preds)
  in
    foldl Map.union Map.empty [sortMap,funMap,predMap]

matches :: Symbol -> RawSymbol -> Bool
matches x                            (ASymbol y)              =  x==y
matches (Symbol idt _)                (AnID di)               = idt==di
matches (Symbol idt CASL.Sign.Sort)        (AKindedId SortKind di) = idt==di
matches (Symbol idt (OpAsItemType _)) (AKindedId FunKind di)  = idt==di
matches (Symbol idt (PredType _))     (AKindedId PredKind di) = idt==di
matches _                            _                        = False

symName :: Symbol -> Id
symName (Symbol idt _) = idt

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

typeToRaw :: SYMB_KIND -> TYPE -> Id -> RawSymbol
typeToRaw _ (O_type _) idt = AKindedId FunKind  idt
typeToRaw _ (P_type _) idt = AKindedId PredKind idt
typeToRaw k (A_type _) idt = symbKindToRaw k idt


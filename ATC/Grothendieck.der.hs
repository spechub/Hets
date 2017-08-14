{-# LANGUAGE UndecidableInstances, FlexibleInstances, OverlappingInstances #-}
{- |
Module      :  ./ATC/Grothendieck.der.hs
Description :  manually created ShATermConvertible instances
Copyright   :  (c) Felix Reckers, C. Maeder, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (existential types)

'ShATermConvertible' instances for data types from "Logic.Grothendieck"
-}

module ATC.Grothendieck where

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import ATerm.AbstractSyntax
import ATerm.Conversion
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Lib.Graph
import Common.LibName
import Common.OrderedMap
import qualified Common.Lib.SizedList as SizedList
import Common.Result

import ATC.GlobalAnnotations ()
import ATC.Graph ()
import ATC.LibName ()
import Logic.Prover
import Data.Typeable
import Data.List
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set

import ATC.Prover ()
import ATC.ExtSign ()
import Static.GTheory

import Control.Monad
import Control.Concurrent.MVar

{-! for Common.AS_Annotation.SenAttr derive : ShATermLG !-}
{-! for Common.AS_Annotation.Annoted derive : ShATermLG !-}
{-! for Logic.Prover.ThmStatus derive : ShATermLG !-}
{-! for Common.GlobalAnnotations.GlobalAnnos derive : ShATermLG !-}
{-! for Common.Lib.Graph.Gr derive : ShATermLG !-}
{-! for Common.Lib.Graph.GrContext derive : ShATermLG !-}
{-! for Common.OrderedMap.ElemWOrd derive : ShATermLG !-}

atcLogicLookup :: LogicGraph -> String -> String -> AnyLogic
atcLogicLookup lg s l =
  propagateErrors " atcLogicLookup"
  $ lookupLogic ("ConvertibleLG " ++ s ++ ":") l lg

-- the same class as ShATermConvertible, but allowing a logic graph as input
class Typeable t => ShATermLG t where
    toShATermLG :: ATermTable -> t -> IO (ATermTable, Int)
    fromShATermLG :: LogicGraph -> Int -> ATermTable -> (ATermTable, t)

toShATermLG' :: ShATermLG t => ATermTable -> t -> IO (ATermTable, Int)
toShATermLG' att t = do
       k <- mkKey t
       m <- getKey k att
       case m of
         Nothing -> do
           (att1, i) <- toShATermLG att t
           setKey k i att1
         Just i -> return (att, i)

fromShATermLG' :: ShATermLG t => LogicGraph -> Int -> ATermTable
               -> (ATermTable, t)
fromShATermLG' lg i att = case getATerm' i att of
        Just d -> (att, d)
        _ -> case fromShATermLG lg i att of
               (attN, t) -> (setATerm' i t attN, t)

-- generic undecidable instance
instance (ShATermConvertible a, Typeable a) => ShATermLG a where
  toShATermLG = toShATermAux
  fromShATermLG _ = fromShATermAux

instance ShATermLG G_basic_spec where
  toShATermLG att0 (G_basic_spec lid basic_spec) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 basic_spec
         return $ addATerm (ShAAppl "G_basic_spec" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_basic_spec" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_basic_spec" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_basic_spec lid i2') }}}
            u -> fromShATermError "G_basic_spec" u

instance ShATermLG G_sign where
  toShATermLG att0 (G_sign lid sign si) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 sign
         (att3, i3) <- toShATermLG' att2 si
         return $ addATerm (ShAAppl "G_sign" [i1, i2, i3] []) att3
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_sign" [i1, i2, i3] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_sign" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                case fromShATermLG' lg i3 att2 of { (att3, i3') ->
                (att3, G_sign lid i2' i3') }}}}
            u -> fromShATermError "G_sign" u

instance ShATermLG G_symbol where
  toShATermLG att0 (G_symbol lid symbol) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 symbol
         return $ addATerm (ShAAppl "G_symbol" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_symbol" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_symbol" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_symbol lid i2') }}}
            u -> fromShATermError "G_symbol" u

instance (Ord a, ShATermLG a) => ShATermLG (G_symbolmap a) where
  toShATermLG att0 (G_symbolmap lid m) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 m
         return $ addATerm (ShAAppl "G_symbolmap" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_symbolmap" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_symbolmap" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_symbolmap lid i2') }}}
            u -> fromShATermError "G_symbolmap" u

instance (Ord a, ShATermLG a) => ShATermLG (G_mapofsymbol a) where
  toShATermLG att0 (G_mapofsymbol lid m) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 m
         return $ addATerm (ShAAppl "G_mapofsymbol" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_mapofsymbol" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_mapofsymbol" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_mapofsymbol lid i2') }}}
            u -> fromShATermError "G_mapofsymbol" u


instance ShATermLG G_symb_items_list where
  toShATermLG att0 (G_symb_items_list lid symb_items) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 symb_items
         return $ addATerm (ShAAppl "G_symb_items_list" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_symb_items_list" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_symb_items_list" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_symb_items_list lid i2') }}}
            u -> fromShATermError "G_symb_items_list" u

instance ShATermLG G_symb_map_items_list where
  toShATermLG att0 (G_symb_map_items_list lid symb_map_items) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 symb_map_items
         return $ addATerm (ShAAppl "G_symb_map_items_list" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_symb_map_items_list" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_symb_map_items_list" i1'
                of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_symb_map_items_list lid i2') }}}
            u -> fromShATermError "G_symb_map_items_list" u

instance ShATermLG G_sublogics where
  toShATermLG att0 (G_sublogics lid sublogics) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 sublogics
         return $ addATerm (ShAAppl "G_sublogics" [i1, i2] []) att2
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_sublogics" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_sublogics" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, G_sublogics lid i2') }}}
            u -> fromShATermError "G_sublogics" u

instance ShATermLG G_morphism where
  toShATermLG att0 (G_morphism lid morphism mi) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 morphism
         (att3, i3) <- toShATermLG' att2 mi
         return $ addATerm (ShAAppl "G_morphism" [i1, i2, i3] []) att3
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "G_morphism" [i1, i2, i3] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "G_morphism" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                case fromShATermLG' lg i3 att2 of { (att3, i3') ->
                (att3, G_morphism lid i2' i3') }}}}
            u -> fromShATermError "G_morphism" u

instance ShATermLG AnyComorphism where
  toShATermLG att0 (Comorphism cid) = do
         (att1, i1) <- toShATermLG' att0 (language_name cid)
         return $ addATerm (ShAAppl "Comorphism" [i1] []) att1
  fromShATermLG lg ix att =
         case getShATerm ix att of
            ShAAppl "Comorphism" [i1] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                (att1, propagateErrors "ATC.Grothendieck.AnyComorphism"
                $ lookupComorphism i1' lg)}
            u -> fromShATermError "AnyComorphism" u

instance ShATermLG GMorphism where
  toShATermLG att0 (GMorphism cid sign1 si morphism2 mi) = do
         (att1, i1) <- toShATermLG' att0 (language_name cid)
         (att2, i2) <- toShATermLG' att1 sign1
         (att3, i3) <- toShATermLG' att2 si
         (att4, i4) <- toShATermLG' att3 morphism2
         (att5, i5) <- toShATermLG' att4 mi
         return $ addATerm (ShAAppl "GMorphism" [i1, i2, i3, i4, i5] []) att5
  fromShATermLG lg ix att =
         case getShATerm ix att of
            ShAAppl "GMorphism" [i1, i2, i3, i4, i5] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case propagateErrors "ATC.Grothendieck.GMorphism"
                  $ lookupComorphism i1' lg of { Comorphism cid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                case fromShATermLG' lg i3 att2 of { (att3, i3') ->
                case fromShATermLG' lg i4 att3 of { (att4, i4') ->
                case fromShATermLG' lg i5 att4 of { (att5, i5') ->
                (att5, GMorphism cid i2' i3' i4' i5') }}}}}}
            u -> fromShATermError "GMorphism" u

instance ShATermLG AnyLogic where
  toShATermLG att0 (Logic lid) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         return $ addATerm (ShAAppl "Logic" [i1] []) att1
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "Logic" [i1] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                (att1, atcLogicLookup lg "AnyLogic" i1') }
            u -> fromShATermError "AnyLogic" u

instance ShATermLG BasicProof where
  toShATermLG att0 (BasicProof lid p) = do
         (att1, i1) <- toShATermLG' att0 (language_name lid)
         (att2, i2) <- toShATermLG' att1 p
         return $ addATerm (ShAAppl "BasicProof" [i1, i2] []) att2
  toShATermLG att0 o = do
         (att1, i1) <- toShATermLG' att0 (show o)
         return $ addATerm (ShAAppl "BasicProof" [i1] []) att1
  fromShATermLG lg ix att = case getShATerm ix att of
            ShAAppl "BasicProof" [i1, i2] _ ->
                case fromShATermLG' lg i1 att of { (att1, i1') ->
                case atcLogicLookup lg "BasicProof" i1' of { Logic lid ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                (att2, BasicProof lid i2') }}}
            v@(ShAAppl "BasicProof" [i1] _) ->
               case fromShATermLG' lg i1 att of { (att1, i1') ->
               (att1, case i1' of
                 "Guessed" -> Guessed
                 "Conjectured" -> Conjectured
                 "Handwritten" -> Handwritten
                 _ -> fromShATermError "BasicProof" v)}
            u -> fromShATermError "BasicProof" u

instance (ShATermLG a) => ShATermLG (Maybe a) where
  toShATermLG att mb = case mb of
        Nothing -> return $ addATerm (ShAAppl "N" [] []) att
        Just x -> do
          (att1, x') <- toShATermLG' att x
          return $ addATerm (ShAAppl "J" [x'] []) att1
  fromShATermLG lg ix att0 =
        case getShATerm ix att0 of
            ShAAppl "N" [] _ -> (att0, Nothing)
            ShAAppl "J" [a] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    (att1, Just a') }
            u -> fromShATermError "Prelude.Maybe" u

instance ShATermLG a => ShATermLG [a] where
   toShATermLG att ts = do
           (att2, inds) <- foldM (\ (att0, l) t -> do
                    (att1, i) <- toShATermLG' att0 t
                    return (att1, i : l)) (att, []) ts
           return $ addATerm (ShAList (reverse inds) []) att2
   fromShATermLG lg ix att0 =
        case getShATerm ix att0 of
            ShAList ats _ ->
                mapAccumL (flip $ fromShATermLG' lg ) att0 ats
            u -> fromShATermError "[]" u

instance (ShATermLG a, ShATermLG b) => ShATermLG (a, b) where
  toShATermLG att0 (x, y) = do
      (att1, x') <- toShATermLG' att0 x
      (att2, y') <- toShATermLG' att1 y
      return $ addATerm (ShAAppl "" [x', y'] []) att2
  fromShATermLG lg ix att0 = case getShATerm ix att0 of
            ShAAppl "" [a, b] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    case fromShATermLG' lg b att1 of { (att2, b') ->
                    (att2, (a', b'))}}
            u -> fromShATermError "(,)" u

instance (ShATermLG a, ShATermLG b, ShATermLG c) => ShATermLG (a, b, c) where
  toShATermLG att0 (x, y, z) = do
      (att1, x') <- toShATermLG' att0 x
      (att2, y') <- toShATermLG' att1 y
      (att3, z') <- toShATermLG' att2 z
      return $ addATerm (ShAAppl "" [x', y', z'] []) att3
  fromShATermLG lg ix att0 = case getShATerm ix att0 of
            ShAAppl "" [a, b, c] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    case fromShATermLG' lg b att1 of { (att2, b') ->
                    case fromShATermLG' lg c att2 of { (att3, c') ->
                    (att3, (a', b', c'))}}}
            u -> fromShATermError "(,,)" u

instance (Ord a, ShATermLG a) => ShATermLG (Set.Set a) where
  toShATermLG att set = do
      (att1, i) <- toShATermLG' att $ Set.toList set
      return $ addATerm (ShAAppl "Set" [i] []) att1
  fromShATermLG lg ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Set" [a] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    (att1, Set.fromDistinctAscList a') }
            u -> fromShATermError "Set.Set" u

instance ShATermLG a => ShATermLG (SizedList.SizedList a) where
  toShATermLG att0 = toShATermLG att0 . SizedList.toList
  fromShATermLG lg ix att0 = case fromShATermLG lg ix att0 of
    (att, l) -> (att, SizedList.fromList l)

instance (Ord a, ShATermLG a, ShATermLG b) => ShATermLG (Map.Map a b) where
  toShATermLG att fm = do
      (att1, i) <- toShATermLG' att $ Map.toList fm
      return $ addATerm (ShAAppl "Map" [i] []) att1
  fromShATermLG lg ix att0 = case getShATerm ix att0 of
            ShAAppl "Map" [a] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    (att1, Map.fromDistinctAscList a') }
            u -> fromShATermError "Map.Map" u

instance (ShATermLG a) => ShATermLG (IntMap.IntMap a) where
  toShATermLG att fm = do
      (att1, i) <- toShATermLG' att $ IntMap.toList fm
      return $ addATerm (ShAAppl "IntMap" [i] []) att1
  fromShATermLG lg ix att0 = case getShATerm ix att0 of
            ShAAppl "IntMap" [a] _ ->
                    case fromShATermLG' lg a att0 of { (att1, a') ->
                    (att1, IntMap.fromDistinctAscList a') }
            u -> fromShATermError "IntMap.IntMap" u


instance ShATermLG G_theory where
  toShATermLG att0 (G_theory lid syn sign si sens ti) = do
         (att1a, i1) <- toShATermLG' att0 (language_name lid)
         (att1, i1a) <- toShATermLG' att1a syn
         (att2, i2) <- toShATermLG' att1 sign
         (att3, i3) <- toShATermLG' att2 si
         (att4, i4) <- toShATermLG' att3 sens
         (att5, i5) <- toShATermLG' att4 ti
         return $ addATerm (ShAAppl "G_theory" [i1, i1a, i2, i3, i4, i5] [])
                att5
  fromShATermLG lg ix att =
         case getShATerm ix att of
            ShAAppl "G_theory" [i1, i1a, i2, i3, i4, i5] _ ->
                case fromShATermLG' lg i1 att of { (att1a, i1') ->
                case atcLogicLookup lg "G_theory" i1' of { Logic lid ->
                case fromShATermLG' lg i1a att1a of { (att1, i1a') ->
                case fromShATermLG' lg i2 att1 of { (att2, i2') ->
                case fromShATermLG' lg i3 att2 of { (att3, i3') ->
                case fromShATermLG' lg i4 att3 of { (att4, i4') ->
                case fromShATermLG' lg i5 att4 of { (att5, i5') ->
                (att5, G_theory lid i1a' i2' i3' i4' i5') }}}}}}}
            u -> fromShATermError "G_theory" u

instance Typeable a => ShATermConvertible (MVar a) where
    toShATermAux att0 _ = return $ addATerm (ShAAppl "MVar" [] []) att0
    fromShATermAux ix att = case getShATerm ix att of
        ShAAppl "MVar" [] _ -> (att, error "ShATermConvertible MVar")
        u -> fromShATermError "MVar" u

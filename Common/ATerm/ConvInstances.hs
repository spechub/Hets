{-# OPTIONS -fno-warn-missing-signatures #-}
{- |
Module      :  $Header$
Description :  special ShATermConvertible instances
Copyright   :  (c) Klaus Lüttich, C. Maeder, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (SPECIALIZE pragma, overlapping Typeable instances)

This module provides instances of `ShATermConvertible`.  The purpose
is separation of the class and those instances that are specialized
for better performance, although specialization does not seem to gain anything.
-}

module Common.ATerm.ConvInstances () where

import Common.ATerm.Conversion
import Common.ATerm.AbstractSyntax
import Common.Lib.Graph as Graph
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Common.OrderedMap as OMap
import qualified Common.InjMap as InjMap
import Common.Id
import Common.Result
import Data.Typeable
import Data.Time (TimeOfDay(..))
import Data.Fixed (Pico)
import Data.Ratio (Ratio)
import System.Time

_tc_InjMapTc = mkTyCon "Common.InjMap.InjMap"

instance (Typeable a,Typeable b) => Typeable (InjMap.InjMap a b) where
    typeOf x = mkTyConApp _tc_InjMapTc [typeOf (geta x),typeOf (getb x)]
      where
        geta :: InjMap.InjMap a b -> a
        geta = undefined
        getb :: InjMap.InjMap a b -> b
        getb = undefined

instance (ShATermConvertible a, Ord a, ShATermConvertible b, Ord b)
    => ShATermConvertible (InjMap.InjMap a b) where
  toShATermAux = toShATermAux_InjMap
  fromShATermAux = fromShATermAux_InjMap

toShATermAux_InjMap att0 m = do
        (att1, a') <- toShATerm' att0 $ InjMap.getAToB m
        (att2, b') <- toShATerm' att1 $ InjMap.getBToA m
        return $ addATerm (ShAAppl "InjMap" [a',b'] []) att2

fromShATermAux_InjMap ix att0 =
        case getShATerm ix att0 of
            ShAAppl "InjMap" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, InjMap.unsafeConstructInjMap a' b') }}
            u -> fromShATermError "InjMap" u

grTc = mkTyCon "Common.Lib.Graph.Gr"

instance (Typeable a, Typeable b) => Typeable (Graph.Gr a b) where
  typeOf s = mkTyConApp grTc
             [ typeOf ((undefined :: Graph.Gr a b -> a) s)
             , typeOf ((undefined :: Graph.Gr a b -> b) s)]

instance (ShATermConvertible a,
          ShATermConvertible b) => ShATermConvertible (Graph.Gr a b) where
  toShATermAux = toShATermAux_Graph
  fromShATermAux = fromShATermAux_Graph

toShATermAux_Graph att0 graph = do
       (att1, a') <- toShATerm' att0 (Graph.convertToMap graph)
       return $ addATerm (ShAAppl "Gr" [a'] []) att1

fromShATermAux_Graph ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Gr" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Graph.unsafeConstructGr a') }
            u -> fromShATermError "Common.Lib.Graph.Gr" u

_tc_GrContextTc = mkTyCon "Common.Lib.Graph.GrContext"

instance (Typeable a,Typeable b) => Typeable (GrContext a b) where
    typeOf x = mkTyConApp _tc_GrContextTc [typeOf (geta x),typeOf (getb x)]
      where
        geta :: GrContext a b -> a
        geta = undefined
        getb :: GrContext a b -> b
        getb = undefined

instance (ShATermConvertible a,
          ShATermConvertible b) => ShATermConvertible (GrContext a b) where
  toShATermAux = toShATermAux_GrContext
  fromShATermAux = fromShATermAux_GrContext

toShATermAux_GrContext att0 (GrContext a b c d) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        (att4, d') <- toShATerm' att3 d
        return $ addATerm (ShAAppl "GrContext" [a',b',c',d'] []) att4
fromShATermAux_GrContext ix att0 =
        case getShATerm ix att0 of
            ShAAppl "GrContext" [a,b,c,d] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    case fromShATerm' d att3 of { (att4, d') ->
                    (att4, GrContext a' b' c' d') }}}}
            u -> fromShATermError "GrContext" u

instance (Ord a, ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (Map.Map a b) where
    {-# SPECIALIZE instance ShATermConvertible (Map.Map Id (Set.Set Id)) #-}
    {-# SPECIALIZE instance (ShATermConvertible a)
           => ShATermConvertible (Map.Map String (OMap.ElemWOrd a)) #-}
    {-# SPECIALIZE instance (ShATermConvertible b, Ord b)
      => ShATermConvertible (Map.Map Id (Set.Set b)) #-}
    toShATermAux = toShATermAux_Map
    fromShATermAux = fromShATermAux_Map

toShATermAux_Map att fm = do
      (att1, i) <- toShATerm' att $ Map.toList fm
      return $ addATerm (ShAAppl "Map" [i] []) att1
fromShATermAux_Map ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Map" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Map.fromDistinctAscList a') }
            u -> fromShATermError "Map.Map" u

instance (ShATermConvertible a)
    => ShATermConvertible (IntMap.IntMap a) where
  toShATermAux = toShATermAux_IntMap
  fromShATermAux = fromShATermAux_IntMap

toShATermAux_IntMap att fm = do
      (att1, i) <- toShATerm' att $ IntMap.toList fm
      return $ addATerm (ShAAppl "IntMap" [i] []) att1
fromShATermAux_IntMap ix att0 =
        case getShATerm ix att0 of
            ShAAppl "IntMap" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, IntMap.fromDistinctAscList a') }
            u -> fromShATermError "IntMap.IntMap" u

elemWOrdTc = mkTyCon "Common.OrderedMap.ElemWOrd"

instance (Typeable a) => Typeable (OMap.ElemWOrd a) where
  typeOf s = mkTyConApp elemWOrdTc
             [typeOf ((undefined :: OMap.ElemWOrd a -> a) s)]

instance (ShATermConvertible a) => ShATermConvertible (OMap.ElemWOrd a) where
  toShATermAux = toShATermAux_ElemWOrd
  fromShATermAux = fromShATermAux_ElemWOrd

toShATermAux_ElemWOrd att0 e = do
       (att1,aa') <- toShATerm' att0 (OMap.order e)
       (att2,bb') <- toShATerm' att1 (OMap.ele e)
       return $ addATerm (ShAAppl "EWOrd"  [ aa' , bb' ] []) att2
fromShATermAux_ElemWOrd ix att0 =
        case getShATerm ix att0 of
            ShAAppl "EWOrd" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, OMap.EWOrd { OMap.order = a', OMap.ele = b'}) }}
            u -> fromShATermError "OMap.ElemWOrd" u

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Set.Set a) where
    {-# SPECIALIZE instance ShATermConvertible (Set.Set Id) #-}
    toShATermAux = toShATermAux_Set
    fromShATermAux = fromShATermAux_Set

toShATermAux_Set att set = do
      (att1, i) <-  toShATerm' att $ Set.toList set
      return $ addATerm (ShAAppl "Set" [i] []) att1
fromShATermAux_Set ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Set" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Set.fromDistinctAscList a') }
            u -> fromShATermError "Set.Set" u

relTc = mkTyCon "Common.Lib.Rel.Rel"

instance (Typeable a) => Typeable (Rel.Rel a) where
  typeOf s = mkTyConApp relTc
             [typeOf ((undefined :: Rel.Rel a -> a) s)]

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Rel.Rel a) where
    {-# SPECIALIZE instance ShATermConvertible (Rel.Rel Id) #-}
    toShATermAux = toShATermAux_Rel
    fromShATermAux = fromShATermAux_Rel

toShATermAux_Rel att rel = do
      (att1, i) <-  toShATerm' att $ Rel.toMap rel
      return $ addATerm (ShAAppl "Rel" [i] []) att1
fromShATermAux_Rel ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Rel" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Rel.fromDistinctMap a') }
            u -> fromShATermError "Rel.Rel" u

instance (ShATermConvertible a) => ShATermConvertible (Maybe a) where
    {-# SPECIALIZE instance ShATermConvertible (Maybe Token) #-}
    toShATermAux = toShATermAux_Maybe
    fromShATermAux = fromShATermAux_Maybe

toShATermAux_Maybe att mb = case mb of
        Nothing -> return $ addATerm (ShAAppl "N" [] []) att
        Just x -> do
          (att1, x') <- toShATerm' att x
          return $ addATerm (ShAAppl "J" [x'] []) att1
fromShATermAux_Maybe ix att0 =
        case getShATerm ix att0 of
            ShAAppl "N" [] _ -> (att0, Nothing)
            ShAAppl "J" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Just a') }
            u -> fromShATermError "Prelude.Maybe" u

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (Either a b) where
    toShATermAux = toShATermAux_Either
    fromShATermAux = fromShATermAux_Either

toShATermAux_Either att0 (Left aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Left" [ aa' ] []) att1
toShATermAux_Either att0 (Right aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Right" [ aa' ] []) att1
fromShATermAux_Either ix att =
        case getShATerm ix att of
            ShAAppl "Left" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Left aa') }
            ShAAppl "Right" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Right aa') }
            u -> fromShATermError "Either" u

instance ShATermConvertible a => ShATermConvertible [a] where
    -- for compound Ids, Set.Set and Rel.Rel
    {-# SPECIALIZE instance ShATermConvertible [Id] #-}
    -- for Id
    {-# SPECIALIZE instance ShATermConvertible [Token] #-}
    -- for Token and all other Strings
    {-# SPECIALIZE instance ShATermConvertible [Char] #-}
    -- for all types in AST with [Pos]
    {-# SPECIALIZE instance ShATermConvertible [Pos] #-}
    toShATermAux = toShATermList'
    fromShATermAux = fromShATermList'

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (a, b) where
    -- for Maps
    {-# SPECIALIZE instance ShATermConvertible (Id, Id) #-}
    {-# SPECIALIZE instance ShATermConvertible (Id, Set.Set Id) #-}
    {-# SPECIALIZE instance ShATermConvertible b
      => ShATermConvertible (Id, b) #-}
    {-# SPECIALIZE instance (Ord b, ShATermConvertible b)
      => ShATermConvertible (Id, Set.Set b) #-}
    -- for Graph nodes
    {-# SPECIALIZE instance ShATermConvertible b
      => ShATermConvertible (Int, b) #-}
    toShATermAux = toShATermAux_Tuple2
    fromShATermAux = fromShATermAux_Tuple2

toShATermAux_Tuple2 att0 (x,y) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      return $ addATerm (ShAAppl "" [x',y'] []) att2
fromShATermAux_Tuple2 ix att0 =
        case getShATerm ix att0 of
            ShAAppl "" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, (a', b'))}}
            u -> fromShATermError "(,)" u

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c)
    => ShATermConvertible (a, b, c) where
    -- for Graph labels
    {-# SPECIALIZE instance ShATermConvertible b
      => ShATermConvertible (Int,b,Int) #-}
    toShATermAux = toShATermAux_Tuple3
    fromShATermAux = fromShATermAux_Tuple3

toShATermAux_Tuple3 att0 (x,y,z) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      (att3, z') <- toShATerm' att2 z
      return $ addATerm (ShAAppl "" [x',y',z'] []) att3
fromShATermAux_Tuple3 ix att0 =
        case getShATerm ix att0 of
            ShAAppl "" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, (a', b', c'))}}}
            u -> fromShATermError "(,,)" u

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c,
          ShATermConvertible d) => ShATermConvertible (a, b, c, d) where
  toShATermAux = toShATermAux_Tuple4
  fromShATermAux = fromShATermAux_Tuple4

toShATermAux_Tuple4 att0 (x,y,z,w) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      (att3, z') <- toShATerm' att2 z
      (att4, w') <- toShATerm' att3 w
      return $ addATerm (ShAAppl "" [x',y',z',w'] []) att4

fromShATermAux_Tuple4 ix att0 =
        case getShATerm ix att0 of
            ShAAppl "" [a,b,c,d] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    case fromShATerm' d att3 of { (att4, d') ->
                    (att4, (a', b', c', d'))}}}}
            u -> fromShATermError "(,,,)" u

_tc_PosTc = mkTyCon "Common.Id.Pos"
instance Typeable Pos where
    typeOf _ = mkTyConApp _tc_PosTc []

_tc_RangeTc = mkTyCon "Common.Id.Range"
instance Typeable Range where
    typeOf _ = mkTyConApp _tc_RangeTc []

_tc_TokenTc = mkTyCon "Common.Id.Token"
instance Typeable Token where
    typeOf _ = mkTyConApp _tc_TokenTc []

_tc_IdTc = mkTyCon "Common.Id.Id"
instance Typeable Id where
    typeOf _ = mkTyConApp _tc_IdTc []

instance ShATermConvertible Pos where
  toShATermAux = toShATermAux_Pos
  fromShATermAux = fromShATermAux_Pos

toShATermAux_Pos att0 (SourcePos a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "P" [a',b',c'] []) att3
fromShATermAux_Pos ix att0 =
        case getShATerm ix att0 of
            ShAAppl "P" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, SourcePos a' b' c') }}}
            u -> fromShATermError "Pos" u

instance ShATermConvertible Range where
  toShATermAux = toShATermAux_Range
  fromShATermAux = fromShATermAux_Range

toShATermAux_Range att0 (Range a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "R" [a'] []) att1
fromShATermAux_Range ix att0 =
        case getShATerm ix att0 of
            ShAAppl "R" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Range a') }
            u -> fromShATermError "Range" u

instance ShATermConvertible Token where
  toShATermAux = toShATermAux_Token
  fromShATermAux = fromShATermAux_Token

toShATermAux_Token att0 (Token a b) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "T" [a',b'] []) att2
fromShATermAux_Token ix att0 =
        case getShATerm ix att0 of
            ShAAppl "T" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, Token a' b') }}
            u -> fromShATermError "Token" u

instance ShATermConvertible Id where
  toShATermAux = toShATermAux_Id
  fromShATermAux = fromShATermAux_Id

toShATermAux_Id att0 (Id a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "I" [a',b',c'] []) att3
fromShATermAux_Id ix att0 =
        case getShATerm ix att0 of
            ShAAppl "I" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, Id a' b' c') }}}
            u -> fromShATermError "Id" u

_tc_DiagKindTc = mkTyCon "Common.Result.DiagKind"
instance Typeable DiagKind where
    typeOf _ = mkTyConApp _tc_DiagKindTc []

_tc_DiagnosisTc = mkTyCon "Common.Result.Diagnosis"
instance Typeable Diagnosis where
    typeOf _ = mkTyConApp _tc_DiagnosisTc []

instance ShATermConvertible DiagKind where
  toShATermAux = toShATermAux_DiagKind
  fromShATermAux = fromShATermAux_DiagKind

toShATermAux_DiagKind att0 Error = do
        return $ addATerm (ShAAppl "Error" [] []) att0
toShATermAux_DiagKind att0 Warning = do
        return $ addATerm (ShAAppl "Warning" [] []) att0
toShATermAux_DiagKind att0 Hint = do
        return $ addATerm (ShAAppl "Hint" [] []) att0
toShATermAux_DiagKind att0 Debug = do
        return $ addATerm (ShAAppl "Debug" [] []) att0
toShATermAux_DiagKind att0 MessageW = do
        return $ addATerm (ShAAppl "MessageW" [] []) att0
fromShATermAux_DiagKind ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Error" [] _ ->
                    (att0, Error)
            ShAAppl "Warning" [] _ ->
                    (att0, Warning)
            ShAAppl "Hint" [] _ ->
                    (att0, Hint)
            ShAAppl "Debug" [] _ ->
                    (att0, Debug)
            ShAAppl "MessageW" [] _ ->
                    (att0, MessageW)
            u -> fromShATermError "DiagKind" u

instance ShATermConvertible Diagnosis where
  toShATermAux = toShATermAux_Diagnosis
  fromShATermAux = fromShATermAux_Diagnosis

toShATermAux_Diagnosis att0 (Diag a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "Diagnosis" [a',b',c'] []) att3
fromShATermAux_Diagnosis ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Diagnosis" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, Diag a' b' c') }}}
            u -> fromShATermError "Diagnosis" u

ctTc = mkTyCon "System.Time.ClockTime"

instance Typeable ClockTime where
  typeOf _ = mkTyConApp ctTc []

instance ShATermConvertible ClockTime where
  toShATermAux = toShATermAux_ClockTime
  fromShATermAux = fromShATermAux_ClockTime

toShATermAux_ClockTime att0 (TOD a b) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "TOD" [a',b'] []) att2
fromShATermAux_ClockTime ix att0 =
        case getShATerm ix att0 of
            ShAAppl "TOD" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, TOD a' b') }}
            u -> fromShATermError "ClockTime" u

timeOfDayTc = mkTyCon "Data.Time.TimeOfDay"

instance Typeable TimeOfDay where
    typeOf _ = mkTyConApp timeOfDayTc []

instance ShATermConvertible TimeOfDay where
  toShATermAux = toShATermAux_TimeOfDay
  fromShATermAux = fromShATermAux_TimeOfDay

toShATermAux_TimeOfDay att0 (TimeOfDay a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 (toRational c :: Rational)
        return $ addATerm (ShAAppl "TimeOfDay" [a',b',c'] []) att3
fromShATermAux_TimeOfDay ix att0 =
        case getShATerm ix att0 of
            ShAAppl "TimeOfDay" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, TimeOfDay a' b'
                     $ (fromRational :: Ratio Integer -> Pico) c') }}}
            u -> fromShATermError "TimeOfDay" u

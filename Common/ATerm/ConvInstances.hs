{-# OPTIONS -fglasgow-exts #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (SPECIALIZE pragma)

This module provides instances of
Common.ATerm.Conversion.ShATermConvertible.  The purpose is separation
of the class and those instances that are specialized for better
performance.
-}

-- specialization does not seem to gain anything

module Common.ATerm.ConvInstances where 

import Common.ATerm.Conversion
import Common.ATerm.AbstractSyntax
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Tree as Tree
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set 
import qualified Common.Lib.Rel as Rel
import qualified Common.OrderedMap as OMap
import Common.Id
import Common.Result

instance (ShATermConvertible a,
          ShATermConvertible b) => ShATermConvertible (Tree.Gr a b) where
    toShATerm att0 graph =
       case toShATerm att0 (labNodes graph) of { (att1,aa') ->
       case toShATerm att1 (labEdges graph) of { (att2,bb') ->
          addATerm (ShAAppl "Graph"  [ aa' , bb' ] []) att2}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Graph" [ aa , bb ] _ ->
                case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                case fromShATerm (getATermByIndex1 bb att) of { bb' ->
                    mkGraph aa' bb' }}
            u -> fromShATermError "Graph" u

instance (Ord a, ShATermConvertible a, ShATermConvertible b) 
    => ShATermConvertible (Map.Map a b) where
    {-# SPECIALIZE instance ShATermConvertible (Map.Map Id (Set.Set Id)) #-}
    {-# SPECIALIZE instance (ShATermConvertible a) 
           => ShATermConvertible (Map.Map String (OMap.ElemWOrd a)) #-}
    {-# SPECIALIZE instance (ShATermConvertible b, Ord b) 
      => ShATermConvertible (Map.Map Id (Set.Set b)) #-}
    toShATerm att fm = case toShATerm att $ Map.toAscList fm of
                       (att1, i) -> addATerm (ShAAppl "Map" [i] []) att1
    fromShATerm att  = case getATerm att of
                       ShAAppl "Map" [i] [] -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           l -> Map.fromDistinctAscList l
                       u -> fromShATermError "Map" u

instance (ShATermConvertible a) => ShATermConvertible (OMap.ElemWOrd a) where
    toShATerm att0 e =
       case toShATerm att0 (OMap.order e) of { (att1,aa') ->
       case toShATerm att1 (OMap.ele e) of { (att2,bb') ->
          addATerm (ShAAppl "EWOrd"  [ aa' , bb' ] []) att2}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "EWOrd" [ aa , bb ] _ ->
                case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                case fromShATerm (getATermByIndex1 bb att) of { bb' ->
                    OMap.EWOrd { OMap.order = aa', OMap.ele = bb' }}}
            u -> fromShATermError "ElemWOrd" u

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Set.Set a) where
    {-# SPECIALIZE instance ShATermConvertible (Set.Set Id) #-}
    toShATerm att set = case  toShATerm att $ Set.toAscList set of
                        (att1, i) -> addATerm (ShAAppl "Set" [i] []) att1
    fromShATerm att  = case getATerm att of
                       ShAAppl "Set" [i] [] -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           l -> Set.fromDistinctAscList l
                       u -> fromShATermError "Set" u

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Rel.Rel a) where
    {-# SPECIALIZE instance ShATermConvertible (Rel.Rel Id) #-}
    toShATerm att rel = case toShATerm att $ Rel.toMap rel of
                        (att1, i) -> addATerm (ShAAppl "Rel" [i] []) att1
    fromShATerm att  = case getATerm att of
                       ShAAppl "Rel" [i] [] -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           m -> Rel.fromDistinctMap m
                       u -> fromShATermError "Rel" u

instance (ShATermConvertible a) => ShATermConvertible (Maybe a) where
    {-# SPECIALIZE instance ShATermConvertible (Maybe Token) #-}
    toShATerm att mb = case mb of
                     Nothing -> addATerm (ShAAppl "N" [] []) att
                     Just x -> case toShATerm att x of
                                  (att1, x') ->
                                   addATerm (ShAAppl "J" [x'] []) att1
    fromShATerm att = case getATerm att of
                      ShAAppl "N" [] _ -> Nothing
                      ShAAppl "J" [x] _ -> 
                           case fromShATerm (getATermByIndex1 x att) of
                           x' -> Just x'
                      aterm -> fromShATermError "Maybe" aterm

instance ShATermConvertible a => ShATermConvertible [a] where
    -- for compound Ids, Set.Set and Rel.Rel
    {-# SPECIALIZE instance ShATermConvertible [Id] #-}
    -- for Id
    {-# SPECIALIZE instance ShATermConvertible [Token] #-}
    -- for Token and all other Strings
    {-# SPECIALIZE instance ShATermConvertible [Char] #-}
    -- for all types in AST with [Pos]
    {-# SPECIALIZE instance ShATermConvertible [Pos] #-}
    toShATerm att l  = toShATermList att l 
    fromShATerm att  = fromShATermList att

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
    toShATerm att0 (x,y) = case toShATerm att0 x of
                           (att1, x') -> 
                             case toShATerm att1 y of
                             (att2, y') -> 
                               addATerm (ShAAppl "" [x',y'] []) att2
    fromShATerm att = case getATerm att of  
                      ShAAppl "" [x, y] _ -> 
                          case fromShATerm (getATermByIndex1 x att) of
                          x' -> case fromShATerm (getATermByIndex1 y att) of
                            y' -> (x',y')
                      at -> fromShATermError "(a,b)" at

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c) 
    => ShATermConvertible (a, b, c) where
    -- for Graph labels
    {-# SPECIALIZE instance ShATermConvertible b 
      => ShATermConvertible (Int,b,Int) #-}
    toShATerm att0 (a,b,c) = case toShATerm att0 a of
                             (att1,x') -> 
                              case toShATerm att1 b of
                              (att2,y') -> 
                               case toShATerm att2 c of
                               (att3,z') -> 
                                  addATerm (ShAAppl "" [x',y',z'] []) att3 
    fromShATerm att = case getATerm att of 
                       ShAAppl "" [a,b,c] _ -> 
                        case fromShATerm (getATermByIndex1 a att) of
                        a' -> 
                         case fromShATerm (getATermByIndex1 b att) of
                         b' ->
                          case fromShATerm (getATermByIndex1 c att) of
                          c' -> (a',b',c')                           
                       at -> fromShATermError "(a,b,c)" at
                            
instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c, 
          ShATermConvertible d) => ShATermConvertible (a, b, c, d) where
    toShATerm att0 (a,b,c,d) = 
        case toShATerm att0 a of
        (att1,a') -> 
            case toShATerm att1 b of
            (att2,b') -> 
                case toShATerm att2 c of
                (att3,c') -> 
                    case toShATerm att3 d of
                    (att4,d') -> 
                        addATerm (ShAAppl "" [a',b',c',d'] []) att4 
    fromShATerm att = 
        case getATerm att of 
        ShAAppl "" [a,b,c,d] _ ->
         case fromShATerm (getATermByIndex1 a att) of
         a' -> 
          case fromShATerm (getATermByIndex1 b att) of
          b' ->
           case fromShATerm (getATermByIndex1 c att) of
           c' -> 
            case fromShATerm (getATermByIndex1 d att) of
            d' -> (a',b',c',d')
        at -> fromShATermError "(a,b,c)" at

instance ShATermConvertible Pos where
    toShATerm att0 (SourcePos a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "P" [a',b',c'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "P" [a,b,c] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    case fromShATerm $ getATermByIndex1 b att of { b' ->
                    case fromShATerm $ getATermByIndex1 c att of { c' ->
                    SourcePos a' b' c' }}}
            u -> fromShATermError "Pos" u

instance ShATermConvertible Range where
    toShATerm att0 (Range a) =
        case toShATerm att0 a of 
        (att1, a') -> addATerm (ShAAppl "R" [a'] []) att1
    fromShATerm att =
        case getATerm att of
            ShAAppl "R" [a] _ -> Range $ fromShATerm $ getATermByIndex1 a att
            u -> fromShATermError "Range" u

instance ShATermConvertible Token where
    toShATerm att0 (Token a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "T" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "T" [a,b] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    case fromShATerm $ getATermByIndex1 b att of { b' ->
                    Token a' b' }}
            u -> fromShATermError "Token" u

instance ShATermConvertible Id where
    toShATerm att0 (Id a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "I" [a',b',c'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "I" [a,b,c] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    case fromShATerm $ getATermByIndex1 b att of { b' ->
                    case fromShATerm $ getATermByIndex1 c att of { c' ->
                    Id a' b' c' }}}
            u -> fromShATermError "Id" u

instance ShATermConvertible DiagKind where
    toShATerm att0 Error =
        addATerm (ShAAppl "Error" [] []) att0
    toShATerm att0 Warning =
        addATerm (ShAAppl "Warning" [] []) att0
    toShATerm att0 Hint =
        addATerm (ShAAppl "Hint" [] []) att0
    toShATerm att0 Debug =
        addATerm (ShAAppl "Debug" [] []) att0
    toShATerm att0 MessageW =
        addATerm (ShAAppl "MessageW" [] []) att0
    fromShATerm att =
        case getATerm att of
            (ShAAppl "Error" [] _) ->
                    Error
            (ShAAppl "Warning" [] _) ->
                    Warning
            (ShAAppl "Hint" [] _) ->
                    Hint
            (ShAAppl "Debug" [] _) ->
                    Debug
            (ShAAppl "MessageW" [] _) ->
                    MessageW
            u -> fromShATermError "DiagKind" u

instance ShATermConvertible Diagnosis where
    toShATerm att0 (Diag a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "Diag" [a',b',c'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "Diag" [a,b,c] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    (Diag a' b' c') }}}
            u -> fromShATermError "Diagnosis" u

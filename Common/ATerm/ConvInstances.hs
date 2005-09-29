{-# OPTIONS -fglasgow-exts #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (SPECIALIZE pragma)

This module provides instances of
Common.ATerm.Conversion.ShATermConvertible.  The purpose is separation
of the class and those instances that are specialized for better
performance.
-}

module Common.ATerm.ConvInstances where 

import Common.ATerm.Conversion
import Common.ATerm.AbstractSyntax
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Tree as Tree
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set 
import qualified Common.Lib.Rel as Rel
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
            (ShAAppl "Graph" [ aa , bb ] _) ->
                case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                case fromShATerm (getATermByIndex1 bb att) of { bb' ->
                    mkGraph aa' bb' }}
            u -> fromShATermError "Graph" u

instance (Ord a, ShATermConvertible a, ShATermConvertible b) 
    => ShATermConvertible (Map.Map a b) where
    {-# SPECIALIZE instance ShATermConvertible (Map.Map Id (Set.Set Id)) #-}
    {-# SPECIALIZE instance (ShATermConvertible b, Ord b) 
      => ShATermConvertible (Map.Map Id (Set.Set b)) #-}
    toShATerm att fm = case toShATerm att $ Map.toAscList fm of
                        (att1,i) ->
                           addATerm (ShAAppl "Map" [i] []) att1
    fromShATerm att  = case aterm of
                       (ShAAppl "Map" [i] []) -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           l -> Map.fromDistinctAscList l
                       u     -> fromShATermError "Map" u
                       where aterm = getATerm att

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Set.Set a) where
    {-# SPECIALIZE instance ShATermConvertible (Set.Set Id) #-}
    toShATerm att set = case  toShATerm att $ Set.toAscList set of
                         (att1,i) ->
                           addATerm (ShAAppl "Set" [i] []) att1
    fromShATerm att  = case aterm of
                       (ShAAppl "Set" [i] []) -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           l -> Set.fromDistinctAscList l
                       u     -> fromShATermError "Set" u
                       where aterm = getATerm att

instance (Ord a,ShATermConvertible a) => ShATermConvertible (Rel.Rel a) where
    {-# SPECIALIZE instance ShATermConvertible (Rel.Rel Id) #-}
    toShATerm att set = case toShATerm att $ Rel.toList set of
                        (att1,i) -> 
                           addATerm (ShAAppl "Rel" [i] []) att1
    fromShATerm att  = case aterm of
                       (ShAAppl "Rel" [i] []) -> 
                           case fromShATerm (getATermByIndex1 i att) of
                           l -> Rel.fromList l
                       u     -> fromShATermError "Rel" u
                       where aterm = getATerm att

instance (ShATermConvertible a) => ShATermConvertible (Maybe a) where
    {-# SPECIALIZE instance ShATermConvertible (Maybe Token) #-}
    toShATerm att mb = case mb of
                     Nothing -> addATerm (ShAAppl "Nothing" [] []) att
                     (Just x)  -> case toShATerm att x of
                                  (att1,x') ->
                                   addATerm (ShAAppl "Just" [x'] []) att1
    fromShATerm att = case aterm of
                       (ShAAppl "Nothing" [] _) -> Nothing
                       (ShAAppl "Just" [x] _) -> 
                           case fromShATerm (getATermByIndex1 x att) of
                           x' -> (Just x')
                       _      -> fromShATermError "Maybe" aterm
                      where aterm = getATerm att


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

instance (ShATermConvertible a,ShATermConvertible b) => ShATermConvertible (a,b) 
    where
    -- for Maps
    {-# SPECIALIZE instance ShATermConvertible (Id,Id) #-}
    {-# SPECIALIZE instance ShATermConvertible (Id,Set.Set Id) #-}
    {-# SPECIALIZE instance ShATermConvertible b => ShATermConvertible (Id,b) #-}
    {-# SPECIALIZE instance (Ord b,ShATermConvertible b) 
      => ShATermConvertible (Id,Set.Set b) #-}
    -- for Graph nodes
    {-# SPECIALIZE instance ShATermConvertible b => ShATermConvertible (Int,b) #-}
    toShATerm att0 (x,y) = case toShATerm att0 x of
                           (att1,x') -> 
                             case toShATerm att1 y of
                             (att2,y') -> 
                               addATerm (ShAAppl "" [x',y'] []) att2
    fromShATerm att = case at of  
                       (ShAAppl "" [x,y] _) -> 
                        case fromShATerm (getATermByIndex1 x att) of
                        x' -> 
                         case fromShATerm (getATermByIndex1 y att) of
                         y' -> (x',y')
                       _  -> fromShATermError "(a,b)" at
                      where at = getATerm att 

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c) 
    => ShATermConvertible (a,b,c) where
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
    fromShATerm att = case at of 
                       (ShAAppl "" [a,b,c] _) -> 
                        case fromShATerm (getATermByIndex1 a att) of
                        a' -> 
                         case fromShATerm (getATermByIndex1 b att) of
                         b' ->
                          case fromShATerm (getATermByIndex1 c att) of
                          c' -> (a',b',c')                           
                       _                 -> fromShATermError "(a,b,c)" at
                      where at = getATerm att
                            
instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c, 
          ShATermConvertible d) => ShATermConvertible (a,b,c,d) where
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
        case at of 
        (ShAAppl "" [a,b,c,d] _) ->
         case fromShATerm (getATermByIndex1 a att) of
         a' -> 
          case fromShATerm (getATermByIndex1 b att) of
          b' ->
           case fromShATerm (getATermByIndex1 c att) of
           c' -> 
            case fromShATerm (getATermByIndex1 d att) of
            d' -> (a',b',c',d')
        _                            -> fromShATermError "(a,b,c)" at
      where at = getATerm att


instance ShATermConvertible Pos where
    toShATerm att0 sourcepos =
        case toShATerm att0 $ sourceName sourcepos of { (att1,aa') ->
        case toShATerm att1 $ sourceLine sourcepos of { (att2,bb') ->
        case toShATerm att2 $ sourceColumn sourcepos of { (att3,cc') ->
          addATerm (ShAAppl "SourcePos"   [ aa' , bb' , cc' ] []) att3}}}
    fromShATerm att =
        case aterm of
            (ShAAppl "SourcePos" [ aa , bb , cc] _) ->
                case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                case fromShATerm (getATermByIndex1 bb att) of { bb' ->
                case fromShATerm (getATermByIndex1 cc att) of { cc' ->
                   newPos aa' bb' cc' }}}
            u -> fromShATermError "SourcePos" u
        where
            aterm = getATerm att

instance ShATermConvertible Range where
    toShATerm att0 (Range l) =
        case toShATerm att0 l of { (att1,aa') ->
          addATerm (ShAAppl "Range"   [ aa' ] []) att1}
    fromShATerm att =
        case aterm of
            (ShAAppl "Range" [ aa ] _) ->
                case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                   Range aa' }
            u -> fromShATermError "Range" u
        where
            aterm = getATerm att

instance ShATermConvertible Token where
    toShATerm att0 (Token aa ab) =
       case toShATerm att0 aa of { (att1,aa') ->
       case toShATerm att1 ab of { (att2,ab') ->
          addATerm (ShAAppl "Token"  [aa',ab'] []) att2 }}
    fromShATerm att =
        case aterm of
            (ShAAppl "Token" [ aa,ab ] _) ->
                let aa' = fromShATerm (getATermByIndex1 aa att)
                    ab' = fromShATerm (getATermByIndex1 ab att)
                    in (Token aa' ab')
            u -> fromShATermError "Token" u
        where
            aterm = getATerm att

instance ShATermConvertible Id where
    toShATerm att0 (Id aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->           
           addATerm (ShAAppl "Id"  [aa',ab',ac'] []) att3 }}}
    fromShATerm att =
        case aterm of
            (ShAAppl "Id" [ aa,ab,ac ] _) ->
                let aa' = fromShATerm (getATermByIndex1 aa att)
                    ab' = fromShATerm (getATermByIndex1 ab att)
                    ac' = fromShATerm (getATermByIndex1 ac att)
                    in (Id aa' ab' ac')
            u -> fromShATermError "Id" u
        where
            aterm = getATerm att

instance ShATermConvertible Diagnosis where
    toShATerm _ _ = error "ConvInstances.toShATerm.Diagnosis"
    fromShATerm _ = error "ConvInstances.fromShaTerm.Diagnosis"
    -- undefined on purpose since all diags should be deleted

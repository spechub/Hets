
{- |

Module      :  $Header$
Copyright   :  (c) Klaus Lüttich 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

This module provides instances of
Common.ATerm.Conversion.ATermConvertible.  The purpose is seperation
of the class and those instances that are specialized for better
performance.


-}

module Common.ATerm.ConvInstances where 

import Common.ATerm.Conversion
import Common.ATerm.AbstractSyntax
import Common.Lib.Parsec.Pos
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set 
import qualified Common.Lib.Rel as Rel
import Common.Id

instance (Ord a, ATermConvertible a, ATermConvertible b) => ATermConvertible (Map.Map a b) where
    {-# SPECIALIZE instance ATermConvertible (Map.Map Id (Set.Set Id)) #-}
    {-# SPECIALIZE instance (ATermConvertible b, Ord b) => ATermConvertible (Map.Map Id (Set.Set b)) #-}
    toATerm fm = let ml = toATerm (Map.toAscList fm)
		       in (AAppl "Map" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Map" [ml] []) -> Map.fromDistinctAscList $ fromATerm ml
		       _ -> fromATermError "Map" at
    toShATerm att fm = case toShATerm att $ Map.toAscList fm of
		        (att1,i) ->
                           addATerm (ShAAppl "Map" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Map" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Map.fromDistinctAscList l
		       u     -> fromShATermError "Map" u
		       where aterm = getATerm att

instance (Ord a,ATermConvertible a) => ATermConvertible (Set.Set a) where
    {-# SPECIALIZE instance ATermConvertible (Set.Set Id) #-}
    toATerm set       = let ml = toATerm (Set.toAscList set)
		        in (AAppl "Set" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Set" [ml] []) -> Set.fromDistinctAscList $ fromATerm ml
		       _ -> fromATermError "Set" at
    toShATerm att set = case  toShATerm att $ Set.toAscList set of
			 (att1,i) ->
                           addATerm (ShAAppl "Set" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Set" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Set.fromDistinctAscList l
		       u     -> fromShATermError "Set" u
		       where aterm = getATerm att

instance (Ord a,ATermConvertible a) => ATermConvertible (Rel.Rel a) where
    {-# SPECIALIZE instance ATermConvertible (Rel.Rel Id) #-}
    toATerm rel       = let ml = toATerm (Rel.toList rel)
		        in (AAppl "Rel" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Rel" [ml] []) -> Rel.fromList $ fromATerm ml
		       _ -> fromATermError "Rel" at
    toShATerm att set = case toShATerm att $ Rel.toList set of
                        (att1,i) -> 
			   addATerm (ShAAppl "Rel" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Rel" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Rel.fromList l
		       u     -> fromShATermError "Rel" u
		       where aterm = getATerm att

instance (ATermConvertible a) => ATermConvertible (Maybe a) where
    {-# SPECIALIZE instance ATermConvertible (Maybe Token) #-}
    toATerm mb = case mb of
                     Nothing -> (AAppl "Nothing" [] [])
                     (Just x)  -> let x' = toATerm x
                                  in (AAppl "Just" [x'] [])
    fromATerm at  = case at of
                     (AAppl "Nothing" [] _) -> Nothing
                     (AAppl "Just" [x] _) -> let x' = fromATerm x
					     in (Just x')
		     _ -> fromATermError "Maybe" at
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


instance ATermConvertible a => ATermConvertible [a] where
    -- for compound Ids, Set.Set and Rel.Rel
    {-# SPECIALIZE instance ATermConvertible [Id] #-}
    -- for Id
    {-# SPECIALIZE instance ATermConvertible [Token] #-}
    -- for Token and all other Strings
    {-# SPECIALIZE instance ATermConvertible [Char] #-}
    -- for all types in AST with [Pos]
    {-# SPECIALIZE instance ATermConvertible [Pos] #-}
    toATerm l        = toATermList l
    fromATerm at     = fromATermList at
    toShATerm att l  = toShATermList att l 
    fromShATerm att  = fromShATermList att

instance (ATermConvertible a,ATermConvertible b) => ATermConvertible (a,b) where
    -- for Maps
    {-# SPECIALIZE instance ATermConvertible (Id,Id) #-}
    {-# SPECIALIZE instance ATermConvertible (Id,Set.Set Id) #-}
    {-# SPECIALIZE instance ATermConvertible b => ATermConvertible (Id,b) #-}
    {-# SPECIALIZE instance (Ord b,ATermConvertible b) => ATermConvertible (Id,Set.Set b) #-}
    -- for Graph nodes
    {-# SPECIALIZE instance ATermConvertible b => ATermConvertible (Int,b) #-}
    toATerm (a,b)    = AAppl "" [toATerm a,toATerm b] []
    fromATerm at     = case at of
                        (AAppl "" [a,b] _) -> (fromATerm a,fromATerm b)
                        _                  -> fromATermError "(a,b)" at
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

instance (ATermConvertible a, ATermConvertible b, ATermConvertible c) => ATermConvertible (a,b,c) where
    -- for Graph labels
    {-# SPECIALIZE instance ATermConvertible b => ATermConvertible (Int,b,Int) #-}
    toATerm (a,b,c) = AAppl "" [toATerm a, toATerm b, toATerm c] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c] _) -> (fromATerm a, fromATerm b, fromATerm c)
                       _                          -> fromATermError "(a,b,c)" at
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
                            
instance (ATermConvertible a, ATermConvertible b, ATermConvertible c, ATermConvertible d) => ATermConvertible (a,b,c,d) where
    toATerm (a,b,c,d) = AAppl "" [toATerm a, toATerm b, toATerm c,toATerm d] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c,d] _) -> (fromATerm a, fromATerm b, fromATerm c, fromATerm d)
                       _                          -> fromATermError "(a,b,c)" at
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


instance ATermConvertible SourcePos where
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
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"SourcePos\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"SourcePos\""

{- ? Generated by DrIFT : Look, but Don't Touch. (works w/ haddock) ? -}
--  Imported from other files :-

instance ATermConvertible Token where
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
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Token\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Token\""

instance ATermConvertible Id where
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
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Id\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Id\""


{- HetCATS/HasCASL/TypeInference.hs
   $Id$
   Author:  Christian Maeder
   Year:    2002

   polymorphic type inference (with type classes) for terms

   limitiations:
   - no subtyping

   - ignore anonymous downsets as classes
   - an intersection class is a (flat) set of class names 

   - no mixfix analysis for types yet

   - use predicate types as in Wadler/Blott 1989 (ad-hoc polymorphism)?

   to do:
   - convert As.Type to Le.Type

  
-}

module TypeInference where

import Id
import Le
import FiniteMap

-- ---------------------------------------------------------------
-- substitution and unification
-- ---------------------------------------------------------------

type Subst = FiniteMap Id Type

applySubst :: Subst -> Type -> Type
applySubst s t =
      case t of
      TypeVar i -> 
	  case lookupFM s i of
	  Nothing -> t
	  Just r -> r
      Type c as -> Type c (map (applySubst s) as)

composeSubst :: Subst -> Subst -> Subst
-- r o s
composeSubst s r = plusFM (mapFM (const $ applySubst r) s)
				       r

occursIn :: Id -> Type -> Bool
-- the initial input term should be no variable
occursIn i t =
    case t of 
    TypeVar i2 -> i == i2
    Type _ as -> any (occursIn i) as

singleSubst :: Id -> Type -> Maybe Subst
-- includes the occurs check
singleSubst i t =
    if i `occursIn` t then Nothing else Just $ unitFM i t 

unify :: Type -> Type -> Maybe Subst
unify t1 t2 =
    case t1 of
    TypeVar i1 -> 
	case t2 of 
	TypeVar i2 -> Just $ if i1 <= i2 then 
		      if i2 <= i1 then emptyFM 
			 else unitFM i1 t2
		      else unitFM i2 t1
	_ -> singleSubst i1 t2
    Type c1 as1 -> 
	case t2 of
	TypeVar i2 -> singleSubst i2 t1
	Type c2 as2 -> if c1 == c2 then
	                  unifyArgs as1 as2
	               else Nothing

unifyArgs :: [Type] -> [Type] -> Maybe Subst
unifyArgs l1 l2 = 
    case l1 of
    [] -> case l2 of
	  [] -> Just emptyFM
	  _ -> Nothing
    t1:r1 -> case l2 of
	     [] -> Nothing
	     t2:r2 -> do s <- unifyArgs r1 r2
			 sh <- unify (applySubst s t1) (applySubst s t2)
			 return $ composeSubst s sh

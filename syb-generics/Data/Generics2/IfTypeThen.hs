{-# OPTIONS -fglasgow-exts #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{-# OPTIONS -fallow-overlapping-instances #-}

{-
 
(C) 2004 Ralf Laemmel
 
Predefined customisation for ifTypeThen.
We cover the normal SYB dichotomy: T, Q, M.
 
-}


module Data.Generics2.IfTypeThen where

import Data.Generics2.Basics


------------------------------------------------------------------------------

-- Transformations

class IfTypeThenT t a
  where
    ifTypeThenT :: t -> a -> a


-- Make a transformation

newtype DictT t a = DictT { dictT :: t -> a -> a }


-- Apply a transformation

applyT :: forall t a . Sat (DictT t a) => t -> a -> a
applyT (t::t) (a::a) = dictT ( dict :: DictT t a ) t a


-- Map transformations to functions

instance IfTypeThenT t a => Sat (DictT t a)
  where
   dict = (DictT $ ifTypeThenT) :: DictT t a


-- A polymorphic default for transformations

instance IfTypeThenT t a
  where
    ifTypeThenT _ = id


------------------------------------------------------------------------------

-- Queries

class IfTypeThenQ q a r | q -> r
  where
    ifTypeThenQ :: q -> a -> r


-- Make a query

newtype DictQ q r a = DictQ { dictQ :: q -> a -> r }


-- Apply a query

applyQ :: forall q r a . Sat (DictQ q r a) => q -> a -> r
applyQ (q::q) (a::a) = r
  where
   r::r = dictQ ( dict :: DictQ q r a ) q a


-- Map queries to functions

instance IfTypeThenQ q a r => Sat (DictQ q r a)
  where
   dict = (DictQ $ ifTypeThenQ) :: DictQ q r a


------------------------------------------------------------------------------

-- Monadic transformations

class Monad m => IfTypeThenM t m a
  where
    ifTypeThenM :: t -> a -> m a


-- Make a monadic transformation

newtype DictM t m a = DictM { dictM :: t -> a -> m a }


-- Apply a monadic transformation

applyM :: forall t m a . (Monad m, Sat (DictM t m a)) => t -> a -> m a
applyM (t::t) (a::a) = r
 where
  r::m a = dictM ( dict :: DictM t m a ) t a


-- Map monadic transformations to functions

instance IfTypeThenM t m a => Sat (DictM t m a)
  where
    dict = (DictM $ ifTypeThenM) :: DictM t m a


-- A polymorphic default for monadic transformations

instance Monad m => IfTypeThenM t m a
  where
    ifTypeThenM _ = return


------------------------------------------------------------------------------

-- Monadic Reads

class Monad m => IfTypeThenR t m a
  where
    ifTypeThenR :: t -> m a


-- Make a monadic read

newtype DictR t m a = DictR { dictR :: t -> m a }


-- Apply a monadic read

applyR :: forall t m a . (Monad m, Sat (DictR t m a)) => t -> m a
applyR (t::t) = r
 where
  r::m a = dictR ( dict :: DictR t m a ) t


-- Map monadic read to functions

instance IfTypeThenR t m a => Sat (DictR t m a)
  where
    dict = (DictR $ ifTypeThenR) :: DictR t m a


-- A polymorphic default for monadic transformations
{-
instance Monad m => IfTypeThenR t m a
  where
    ifTypeThenM _ = return
-}

{-# OPTIONS -fglasgow-exts #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{-# OPTIONS -fallow-overlapping-instances #-}

{-

(C) 2004 Ralf Laemmel

Traversal schemes parameterised in context.

-}


module Data.Generics2.CtxSchemes

where

import Data.Generics2.Basics
import Data.Generics2.IfTypeThen
import Data.List

------------------------------------------------------------------------------

-- Traversal schemes

glength :: ctx () -> GenericQ ctx Int
glength ctx = length . gmapQ ctx (const ())

everywhere :: ctx () -> GenericT ctx -> GenericT ctx
everywhere ctx f
  = f . gmapT ctx (everywhere ctx f)

everywhereBut :: ctx () -> GenericQ ctx Bool -> GenericT ctx -> GenericT ctx
everywhereBut ctx q f x
    | q x       = x
    | otherwise = f (gmapT ctx (everywhereBut ctx q f) x)

everything :: ctx () -> (r -> r -> r) -> GenericQ ctx r -> GenericQ ctx r
everything ctx k f x
  = foldl k (f x) (gmapQ ctx (everything ctx k f) x)

everyone :: ctx () -> GenericQ ctx r -> GenericQ ctx [r]
everyone ctx q x = gmapQ ctx q x ++ (concat $ gmapQ ctx (everyone ctx q) x)

everyoneBut :: ctx () -> GenericQ ctx Bool -> GenericQ ctx r -> GenericQ ctx [r]
everyoneBut ctx p q x = (concatMap (\(x, y) -> if x then [y] else []) $ zip (gmapQ ctx p x) (gmapQ ctx q x)) ++ (concat $ gmapQ ctx (everyoneBut ctx p q) x)

gcountif :: ctx () -> GenericQ ctx Bool -> GenericQ ctx Int
gcountif ctx cond a
  = (foldr (+) (if cond a then 1 else 0)
               (gmapQ ctx (gcountif ctx cond) a))


------------------------------------------------------------------------------

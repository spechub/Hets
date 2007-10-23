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
import Data.List

------------------------------------------------------------------------------

-- Traversal schemes

glength :: ctx () -> GenericQ ctx Int
glength ctx = length . gmapQ ctx (const ())

everyone :: ctx () -> GenericQ ctx r -> GenericQ ctx [r]
everyone ctx q x = gmapQ ctx q x ++ (concat $ gmapQ ctx (everyone ctx q) x)


------------------------------------------------------------------------------

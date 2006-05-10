{-# OPTIONS -fglasgow-exts #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{-# OPTIONS -fallow-overlapping-instances #-}

{-

(C) 2004 Ralf Laemmel

Context parameterisation and context passing.

-}


module Data.Context

where

------------------------------------------------------------------------------

--
-- The Sat class from John Hughes' "Restricted Data Types in Haskell"
--

class Sat a
  where
    dict :: a


------------------------------------------------------------------------------

-- No context

data NoCtx a

noCtx = undefined::NoCtx ()

instance Sat (NoCtx a) where dict = undefined


------------------------------------------------------------------------------

-- Pair context

data PairCtx l r a
   = PairCtx { leftCtx  :: l a
             , rightCtx :: r a }

pairCtx (l::l ()) (r::r ())
  = undefined::PairCtx l r ()

instance (Sat (l a), Sat (r a))
      => Sat (PairCtx l r a)
  where
    dict = PairCtx { leftCtx  = dict
                   , rightCtx = dict }


------------------------------------------------------------------------------

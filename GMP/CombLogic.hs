{-# OPTIONS -fglasgow-exts #-}
module Experiment where

data Boole a = And a a | Not a
data Box c a = Box c (Boole a)
data BBox c a = BBox c (Boole a) (Boole a)
data WBForm = WBForm (Box W (BWForm))
data BWForm = BWForm (Box B (WBForm))

data W = W
data B = B

class Form a b c | a->b, a->c where
  extract :: Form a b c => a -> Box b c
  provable :: Form a b c => a -> Bool

instance Form WBForm W BWForm
instance Form BWForm B WBForm

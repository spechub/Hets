{-# LANGUAGE DeriveDataTypeable #-}
{-
this file is a template for MMT:
Signatures and Theories remain static,
only inserting Logic name here
-}
module PLpatt.Sign where

import Data.Typeable
import Common.Result
import Data.List
import PLpatt.AS_BASIC_PLpatt

-- Decl and Form are fixed
data Sigs = Sigs [Decl] deriving (Show, Typeable)
data Theo = Theo{sign :: Sigs,axioms :: [Bool']} deriving (Show, Typeable)

sigDiff :: Sigs -> Sigs -> Result Sigs
sigDiff (Sigs dcl1) (Sigs dcl2) = Result [] $ Just $ Sigs (dcl1 \\ dcl2)


{-
this file is a template for MMT:
Signatures and Theories remain static,
only inserting Logic name here
-}
module PLpatt.Sign where

import PLpatt.AS_BASIC_PLpatt
-- import Common.Id

-- Decl and Form are fixed
data Sigs = Sigs [Decl]
data Theo = Theo{sign :: Sigs,axioms :: [Form]} 

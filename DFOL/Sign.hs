{- |
Module      :  $Header$
Description :  Definition of signatures for first-order logic with dependent types (DFOL)
-}

module DFOL.Sign where

import Common.Doc
import Common.DocUtils

-- signatures for DFOL - so far just the empty signature
data Sign = EmptySig deriving (Show, Eq, Ord)

-- the empty signature
emptySig :: Sign
emptySig = EmptySig

-- determines whether a signature is valid
isValidSig :: Sign -> Bool
isValidSig _ = True 

-- pretty printing
instance Pretty Sign where
   pretty = printSig

printSig :: Sign -> Doc
printSig EmptySig = text "Empty"

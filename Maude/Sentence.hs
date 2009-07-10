{- |
Module      :  $Header$
Description :  Sentences for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of sentences for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Sentence where

import Maude.AS_Maude

import Maude.Printing

import Common.Doc
import Common.DocUtils

data Sentence = Membership Membership
              | Equation Equation
              | Rule Rule
    deriving (Show, Read, Ord, Eq)
    
instance Pretty Sentence where
  pretty (Membership mb) = text $ printMb mb
  pretty (Equation eq) = text $ printEq eq
  pretty (Rule rl) = text $ printRl rl
  

-- | extract the Sentences of a Module
getSentences :: Spec -> [Sentence]
getSentences (Spec _ _ stmts) = let
            insert stmt = case stmt of
                MbStmnt mb -> (++) [Membership mb]
                EqStmnt eq -> (++) [Equation eq]
                RlStmnt rl -> (++) [Rule rl]
                _ -> (++) []
        in foldr insert [] stmts

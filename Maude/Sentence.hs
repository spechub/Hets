{- |
Module      :  $Header$
Description :  Sentences for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of sentences for Maude.
-}

module Maude.Sentence (
    Sentence(..),
    fromSpec,
    isRule,
) where


import Maude.AS_Maude
import Maude.Meta
import Maude.Printing ()

import Data.Maybe (mapMaybe)

import Common.Doc (vsep)
import Common.DocUtils (Pretty(..))


data Sentence = Membership Membership
              | Equation Equation
              | Rule Rule
    deriving (Show, Read, Ord, Eq)


instance Pretty Sentence where
    pretty sent = case sent of
        Membership mb -> pretty mb
        Equation eq   -> pretty eq
        Rule rl       -> pretty rl
    pretties = vsep . map pretty


instance HasSorts Sentence where
    getSorts sen = case sen of
        Membership mb -> getSorts mb
        Equation eq   -> getSorts eq
        Rule rl       -> getSorts rl
    mapSorts mp sen = case sen of
        Membership mb -> Membership $ mapSorts mp mb
        Equation eq   -> Equation $ mapSorts mp eq
        Rule rl       -> Rule $ mapSorts mp rl

instance HasOps Sentence where
    getOps sen = case sen of
        Membership mb -> getOps mb
        Equation eq   -> getOps eq
        Rule rl       -> getOps rl
    mapOps mp sen = case sen of
        Membership mb -> Membership $ mapOps mp mb
        Equation eq   -> Equation $ mapOps mp eq
        Rule rl       -> Rule $ mapOps mp rl

instance HasLabels Sentence where
    getLabels sen = case sen of
        Membership mb -> getLabels mb
        Equation eq   -> getLabels eq
        Rule rl       -> getLabels rl
    mapLabels mp sen = case sen of
        Membership mb -> Membership $ mapLabels mp mb
        Equation eq   -> Equation $ mapLabels mp eq
        Rule rl       -> Rule $ mapLabels mp rl


-- | Extract the |Sentence|s of a |Module|
fromSpec :: Module -> [Sentence]
fromSpec (Module _ _ stmts) = let
        convert stmt = case stmt of
            MbStmnt mb -> Just $ Membership mb
            EqStmnt eq -> Just $ Equation eq
            RlStmnt rl -> Just $ Rule rl
            _ -> Nothing
    in mapMaybe convert stmts

-- | Check whether a |Sentence| is a |Rule|
isRule :: Sentence -> Bool
isRule sent = case sent of
    Rule _ -> True
    _      -> False

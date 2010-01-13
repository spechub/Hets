{- |
Module      :  $Header$
Description :  Maude Sentences
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of sentences for Maude.
-}

module Maude.Sentence (
    -- * Types
    -- ** The Sentence type
    Sentence(..),
    -- * Contruction
    fromSpec,
    fromStatements,
    -- * Testing
    isRule,
) where

import Maude.AS_Maude
import Maude.Meta
import Maude.Printing ()

import Common.Id (mkSimpleId, GetRange)
import Common.Doc (vcat)
import Common.DocUtils (Pretty(..))

-- * Types

-- ** The Sentence type
-- | A 'Membership', 'Equation' or 'Rule'.
data Sentence = Membership Membership
              | Equation Equation
              | Rule Rule
              deriving (Show, Read, Ord, Eq)

-- ** Sentence Instances

instance GetRange Sentence

instance Pretty Sentence where
    pretty sent = case sent of
        Membership mb -> pretty mb
        Equation eq   -> pretty eq
        Rule rl       -> pretty rl
    pretties = vcat . map pretty

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

-- * Contruction

-- | Extract the 'Sentence's from the given 'Module'.
fromSpec :: Module -> [Sentence]
fromSpec (Module _ _ stmts) = fromStatements stmts

-- | Extract the 'Sentence's from the given 'Statement's.
fromStatements :: [Statement] -> [Sentence]
fromStatements stmts = let
    convert stmt = case stmt of
        SubsortStmnt sub -> [fromSubsort sub]
        OpStmnt op -> fromOperator op
        MbStmnt mb -> [Membership mb]
        EqStmnt eq -> [Equation eq]
        RlStmnt rl -> [Rule rl]
        _ -> []
    in concatMap convert stmts

fromSubsort :: SubsortDecl -> Sentence
fromSubsort (Subsort s1 s2) = Membership mb
    where var = mkVar "V" (TypeSort s1)
          cond = MbCond var s1
          mb = Mb var s2 [cond] []

fromOperator :: Operator -> [Sentence]
fromOperator (Op op dom cod attrs) = let
    name = getName op
    first = head dom
    second = head $ tail dom
    convert attr = case attr of
        Assoc -> assocEq name first second cod
        Comm -> commEq name first second cod
        Idem -> idemEq name first cod
        Id term -> identityEq name first term cod
        LeftId term -> leftIdEq name first term cod
        RightId term -> rightIdEq name first term cod
        _ -> []
    in concatMap convert attrs

commEq :: Qid -> Type -> Type -> Type -> [Sentence]
commEq op ar1 ar2 co = [Equation $ Eq t1 t2 [] []]
    where v1 = mkVar "v1" ar1
          v2 = mkVar "v2" ar2
          t1 = Apply op [v1, v2] co
          t2 = Apply op [v2, v1] co

assocEq :: Qid -> Type -> Type -> Type -> [Sentence]
assocEq op ar1 ar2 co = [eq]
    where v1 = mkVar "v1" ar1
          v2 = mkVar "v2" ar2
          v3 = mkVar "v3" ar2
          t1 = Apply op [v1, v2] co
          t2 = Apply op [t1, v3] co
          t3 = Apply op [v2, v3] co
          t4 = Apply op [v1, t3] co
          eq = Equation $ Eq t2 t4 [] []

idemEq :: Qid -> Type -> Type -> [Sentence]
idemEq op ar co = [Equation $ Eq t v [] []]
    where v = Apply (mkSimpleId "v") [] ar
          t = Apply op [v, v] co

identityEq :: Qid -> Type -> Term -> Type -> [Sentence]
identityEq op ar1 idt co = [eq1, eq2]
    where v = mkVar "v" ar1
          t1 = Apply op [v, idt] co
          t2 = Apply op [idt, v] co
          eq1 = Equation $ Eq t1 v [] []
          eq2 = Equation $ Eq t2 v [] []

leftIdEq :: Qid -> Type -> Term -> Type -> [Sentence]
leftIdEq op ar1 idt co = [eq1, eq2]
    where v = mkVar "v" ar1
          t = Apply op [idt, v] co
          eq1 = Equation $ Eq t v [] []
          eq2 = Equation $ Eq v t [] []

rightIdEq :: Qid -> Type -> Term -> Type -> [Sentence]
rightIdEq op ar1 idt co = [eq1, eq2]
    where v = mkVar "v" ar1
          t = Apply op [v, idt] co
          eq1 = Equation $ Eq t v [] []
          eq2 = Equation $ Eq v t [] []

-- * Testing

-- | True iff the given 'Sentence' is a 'Rule'.
isRule :: Sentence -> Bool
isRule sent = case sent of
    Rule _ -> True
    _      -> False

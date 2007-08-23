{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Signature for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for propositional logic
-}
{-
  Ref.

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Sign 
    (
     Sign (..)                     -- Propositional Signatures
    ,pretty                        -- pretty printing
    ,isLegalSignature              -- is a signature ok?
    ,addToSig                      -- adds an id to the given Signature
    ,unite                         -- union of sigantures
    ,emptySig                      -- empty signature
    ,isSubSigOf                    -- is subsiganture?
    ,sigDiff                       -- Difference of Signatures
    ,sigUnion                      -- Union for Logic.Logic
    ,diffOfSigs                    -- Difference for Logic.Logic
    ,ATP_ProofTree (..)            -- Proof tree for propositonal logic
    ,emptyProofTree                -- the empty proof tree
    ) where

import qualified Data.Set as Set
import qualified Common.Id as Id
import qualified Common.Result as Result
import Common.Doc
import Common.DocUtils

-- | Datatype for propositional Signatures
-- Signatures are just sets
newtype Sign = Sign {items :: Set.Set Id.Id}
          deriving (Eq, Show)

instance Pretty Sign where
    pretty = printSign

-- | determines whether a signature is vaild
-- all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s = hsep [text "prop", (sepByCommas $ map pretty (Set.toList $ items s))]

-- | Adds an Id to the signature
addToSig :: Sign -> Id.Id -> Sign 
addToSig sig tok = Sign {items = Set.insert tok $ items sig}

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign
                  {
                    items = Set.union (items sig1) (items sig2)
                  }

-- | The empty signature
emptySig :: Sign
emptySig = Sign{items = Set.empty}

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 = Set.isSubsetOf (items sig1) (items sig2)

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign{items = Set.difference (items sig1) (items sig2)}

-- | union of Signatures
-- or do I have to care about more things here?
sigUnion :: Sign -> Sign -> Result.Result Sign
sigUnion s1 s2 = Result.Result 
                 {
                   Result.diags = [Result.Diag
                            {
                              Result.diagKind   = Result.Debug
                            , Result.diagString = "All fine sigUnion"
                            , Result.diagPos    = Id.nullRange
                            }]
                 , Result.maybeResult = Just $ unite s1 s2
                 }

-- | difference of signatures for Logic.Logic
-- uses sigDiff
diffOfSigs :: Sign -> Sign -> Result.Result Sign
diffOfSigs s1 s2 
    | isSubSigOf s1 s2 = Result.Result 
                         {
                           Result.diags = [Result.Diag
                                           {
                                             Result.diagKind   = Result.Debug
                                           , Result.diagString = "All fine diffOfSigs"
                                           , Result.diagPos    = Id.nullRange
                                           }]
                         , Result.maybeResult = Just $ sigDiff s1 s2
                         }
    | otherwise         = Result.Result 
                         {
                           Result.diags = [Result.Diag
                                           {
                                             Result.diagKind   = Result.Debug
                                           , Result.diagString = (show $ pretty s1) ++
                                                                 " not subsignatue of " ++
                                                                 (show $ pretty s2)
                                           , Result.diagPos    = Id.nullRange
                                           }]
                         , Result.maybeResult = Nothing
                         }

-- ** Propositional proof tree

{- |
  Datatype for storing of the proof tree. The Show class is instantiated.
-}
data ATP_ProofTree = ATP_ProofTree String
       deriving (Eq, Ord)

instance Show ATP_ProofTree where
  show (ATP_ProofTree st) = st

emptyProofTree :: ATP_ProofTree 
emptyProofTree = ATP_ProofTree ""

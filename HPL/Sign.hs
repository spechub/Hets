{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPL/Sign.hs
Description :  Signature for hybrid propositional logic
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

  Definition of signatures for hybrid propositional logic

  
-}

module HPL.Sign
    (HSign (..)                     -- Propositional Signatures
    --, id2SimpleId
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    , addPropToSig                   
    , addNomToSig
    , unite                         -- union of signatures
    , emptySig                      -- empty signature
    , isSubSigOf                    -- is subsignature?
    , sigDiff                       -- Difference of Signatures
    , sigUnion                      -- Union for Logic.Logic
    ) where

import Data.Data
import qualified Data.Set as Set

import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

import qualified Propositional.Sign as PSign

{- | Datatype for hybrid propositional Signatures
Signatures consist of a propositional signature and a set of nominals.
There is only one modality so we don't represent it 
explicitly in the signature. -}
data HSign = HSign {
                  propSig :: PSign.Sign,
                  noms :: Set.Set Id}
  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty HSign where
    pretty = printSign

{- | determines whether a signature is vaild
a signature is not legal when the same name is used for
both a nominal and a proposition-}
isLegalSignature :: HSign -> Bool
isLegalSignature sig = let
  propSet = PSign.items $ propSig sig
  nomsSet = noms sig
 in Set.intersection propSet nomsSet == Set.empty

-- | pretty printing for signatures
printSign :: HSign -> Doc
printSign s =
    PSign.printSign (propSig s)
    $+$
    hsep [text "states", sepByCommas $ map pretty $ Set.toList $ noms s]

-- | Adds a nominal to the signature
addNomToSig :: HSign -> Id -> HSign
addNomToSig sig nom = sig {noms = Set.insert nom $ noms sig}

-- | Adds a proposition to the signature
addPropToSig :: HSign -> Id -> HSign
addPropToSig sig p = sig {propSig = PSign.addToSig (propSig sig) p}

-- | Union of signatures
-- TODO: fail if the union is not legal, i.e. one signature has a prop x and the other, a nominal xs
unite :: HSign -> HSign -> HSign
unite sig1 sig2 = HSign {
                    propSig = PSign.unite (propSig sig1) $ propSig sig2,
                    noms = Set.union (noms sig1) $ noms sig2}

-- | The empty signature
emptySig :: HSign
emptySig = HSign {propSig = PSign.emptySig,
                  noms = Set.empty}

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: HSign -> HSign -> Bool
isSubSigOf sig1 sig2 = 
           (PSign.isSubSigOf (propSig sig1) $ propSig sig2)  
           && (Set.isSubsetOf (noms sig1) $ noms sig2)

-- | difference of Signatures
sigDiff :: HSign -> HSign -> HSign
sigDiff sig1 sig2 = HSign {
                     propSig = PSign.sigDiff (propSig sig1) $ propSig sig2,
                     noms = Set.difference (noms sig1) $ noms sig2}

-- | union of Signatures
sigUnion :: HSign -> HSign -> Result HSign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
    . Just . unite s1


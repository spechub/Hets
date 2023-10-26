{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPAR/Sign.hs
Description :  Signature for hybrid partial algebras
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

  Definition of signatures for hybrid partial algebras

  
-}

module HPAR.Sign
    (HSign (..)                     -- signatures
    --, id2SimpleId
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    --, addPropToSig                   
    , addNomToSig
    , addModToSig
    --, unite                         -- union of signatures
    , emptySig                      -- empty signature
    , isSubSigOf                    -- is subsignature?
    , sigDiff                       -- Difference of Signatures
    , sigUnion                      -- Union for Logic.Logic
    , symOf                         -- symbols of a signature
    ) where

import Data.Data
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

import qualified RigidCASL.Sign as PARSign
import RigidCASL.Print_AS ()
import qualified CASL.Sign as CSign

import Logic.Logic
import qualified RigidCASL.Logic_RigidCASL as Base

{- | Datatype for hybrid propositional Signatures
Signatures consist of a propositional signature and a set of nominals.
-}
data HSign = HSign {
                  baseSig :: PARSign.RSign,
                  noms :: Set.Set Id,
                  mods :: Map.Map Id Int}
  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty HSign where
    pretty = printSign

{- | determines whether a signature is vaild
a signature is not legal when the same name is used for
both a nominal and a proposition-}
isLegalSignature :: HSign -> Bool
isLegalSignature sig = let
  -- propSet = PSign.items $ propSig sig
  nomsSet = noms sig
  modsSet = Map.keysSet $ mods sig
 in -- Set.intersection propSet nomsSet == Set.empty &&
    Set.intersection nomsSet modsSet == Set.empty
 -- TODO: improve - noms and mods must be disjoint with the signature too

-- | pretty printing for signatures
printSign :: HSign -> Doc
printSign s = 
    let bsig = baseSig s in 
    pretty (bsig {CSign.sortRel = Rel.difference (Rel.transReduce $ CSign.sortRel bsig)
                             . Rel.transReduce $ Rel.fromSet $ Set.map (\x->(x,x)) $ PARSign.rigidSorts $ CSign.extendedInfo bsig,
                  CSign.opMap = CSign.diffOpMapSet (CSign.opMap bsig) $ PARSign.rigidOps $ CSign.extendedInfo bsig,
                  CSign.predMap = CSign.diffMapSet (CSign.predMap bsig) $ PARSign.rigidPreds $ CSign.extendedInfo bsig})
    -- this ensures that the rigid symbols are not displayed as non-rigid
    $+$
    let nomss = Set.toList $ noms s in
    case nomss of 
     [] -> empty
     _ -> hsep [text ("nominal" ++ (case nomss of 
                              [_] -> ""
                              _ -> "s")), sepByCommas $ map pretty nomss]
    $+$
    (foldl (\aDoc (i,n) -> aDoc $+$ 
                            hsep [text ( case Map.toList $ mods s of 
                                           [_] -> "modality"
                                           _ -> "modalities"
                                       ),
                                  pretty i, 
                                  text ":", 
                                  pretty n]) empty $ Map.toList $ mods s)
    -- hsep [text "modality", sepByCommas $ map pretty $ Set.toList $ noms s]


-- | Adds a nominal to the signature
addNomToSig :: HSign -> Id -> Result HSign
addNomToSig sig nom = 
 let 
  snoms = noms sig
 in if Set.member nom snoms then Result [mkDiag Warning "redeclaring nominal" nom] $ Just sig
    else return sig {noms = Set.insert nom snoms}

-- | Adds a modality to the signature
addModToSig :: HSign -> Id -> Int -> Result HSign
addModToSig sig md ar = 
 let
  smods = mods sig
 in if Map.member md smods then Result [mkDiag Warning "redeclaring modality" md] $ Just sig  
     else return sig {mods = Map.insert md ar smods}

-- | The empty signature
emptySig :: HSign
emptySig = HSign {
             baseSig = CSign.emptySign PARSign.emptyRigidExt,
             noms = Set.empty,
             mods = Map.empty}

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: HSign -> HSign -> Bool
isSubSigOf sig1 sig2 =
         (is_subsig (Base.RigidCASL) (baseSig sig1) $ baseSig sig2)
         --(CSign.isSubSig PARSign.isSubRigidExt (baseSig sig1) $ baseSig sig2)
         &&
         (Set.isSubsetOf (noms sig1) $ noms sig2)
         && 
         (Set.isSubsetOf (modSet sig1) $ modSet sig2)
   where
     modSet sig = Set.fromList $ Map.toList $ mods sig

-- | difference of Signatures
sigDiff :: HSign -> HSign -> HSign
sigDiff _sig1 _sig2 = undefined 
                    --HSign {
                    -- propSig = PSign.sigDiff (propSig sig1) $ propSig sig2,
                    -- noms = Set.difference (noms sig1) $ noms sig2}

-- | union of Signatures
sigUnion :: HSign -> HSign -> Result HSign
sigUnion = undefined

symOf :: HSign -> Set.Set CSign.Symbol
symOf _sig = undefined

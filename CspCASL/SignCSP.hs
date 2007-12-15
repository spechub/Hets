{- |
Module      :  $Id$
Description :  CspCASL signatures
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

signatures for CSP-CASL

-}

-- todo:  implement isInclusion, computeExt

module CspCASL.SignCSP where

import qualified Data.Map as Map
import qualified Data.Set as Set

import CASL.AS_Basic_CASL (SORT)
import CASL.Sign (emptySign, Sign)
import CASL.Morphism (Morphism)
import qualified Common.Doc as Doc
import qualified Common.DocUtils as DocUtils
import Common.Id (Id)

import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)

-- | A process has zero or more parameter sorts, and a communication
-- alphabet.
data ProcProfile = ProcProfile
    { procArgs :: [SORT]
    , procAlphabet :: ProcAlpha
    } deriving (Eq, Show)

-- | A process communication alphabet consists of a set of sort names
-- and a set of channel names.
data ProcAlpha = ProcAlpha
    { procAlphaSorts :: Set.Set SORT
    , procAlphaChannels :: Set.Set CHANNEL_NAME
    } deriving (Eq, Show)

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map PROCESS_NAME ProcProfile

-- | CSP process signature.
data CspProcSign = CspProcSign
    { chans :: ChanNameMap
    , procs :: ProcNameMap
    } deriving (Eq, Show)

-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CspSign = Sign () CspProcSign

-- | Empty CspCASL signature.
emptyCspSign :: CspSign
emptyCspSign = emptySign emptyCspProcSign

-- | Empty CSP process signature.
emptyCspProcSign :: CspProcSign
emptyCspProcSign = CspProcSign
    { chans = Map.empty
    , procs = Map.empty
    }

-- | Compute union of two CSP process signatures.
addCspProcSig :: CspProcSign -> CspProcSign -> CspProcSign
addCspProcSig a b =
    a { chans = chans a `Map.union` chans b
      , procs = procs a `Map.union` procs b
      }

-- XXX looks incomplete!
isInclusion :: CspProcSign -> CspProcSign -> Bool
isInclusion _ _ = True



-- XXX morphisms between CSP process signatures?

data CspAddMorphism = CspAddMorphism
    { channelMap :: Map.Map Id Id
    , processMap :: Map.Map Id Id
    } deriving (Eq, Show)

type CspMorphism = Morphism () CspProcSign CspAddMorphism

emptyCspAddMorphism :: CspAddMorphism
emptyCspAddMorphism = CspAddMorphism
  { channelMap = Map.empty -- ???
  , processMap = Map.empty
  }

-- dummy instances, need to be elaborated!
instance DocUtils.Pretty CspProcSign where
  pretty = Doc.text . show
instance DocUtils.Pretty CspAddMorphism where
  pretty = Doc.text . show

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

import qualified CASL.AS_Basic_CASL as AS_Basic_CASL
import qualified CASL.Sign
import qualified CASL.Morphism
import qualified Common.Doc as Doc
import qualified Common.DocUtils as DocUtils
import qualified Common.Id as Id

-- | A CSP process signature contains information on channels and
-- processes.
data CspProcSign = CspProcSign
    { chans :: Map.Map Id.Id AS_Basic_CASL.SORT
    , procs :: Map.Map Id.Id (Maybe AS_Basic_CASL.SORT)
    } deriving (Eq, Show)

-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CSPSign = CASL.Sign.Sign () CspProcSign

-- | Empty CspCASL signature.
emptyCSPSign :: CSPSign
emptyCSPSign = CASL.Sign.emptySign emptyCspProcSign

-- | Empty CSP process signature.
emptyCspProcSign :: CspProcSign
emptyCspProcSign = CspProcSign
    { chans = Map.empty
    , procs = Map.empty
    }

-- | Compute difference between two CSP process signatures.
diffCspProcSig :: CspProcSign -> CspProcSign -> CspProcSign
diffCspProcSig a b =
    a { chans = chans a `Map.difference` chans b
      , procs = procs a `Map.difference` procs b
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

data CSPAddMorphism = CSPAddMorphism
    { channelMap :: Map.Map Id.Id Id.Id
    , processMap :: Map.Map Id.Id Id.Id
    } deriving (Eq, Show)

type CSPMorphism = CASL.Morphism.Morphism () CspProcSign CSPAddMorphism

emptyCSPAddMorphism :: CSPAddMorphism
emptyCSPAddMorphism = CSPAddMorphism
  { channelMap = Map.empty -- ???
  , processMap = Map.empty
  }

-- dummy instances, need to be elaborated!
instance DocUtils.Pretty CspProcSign where
  pretty = Doc.text . show
instance DocUtils.Pretty CSPAddMorphism where
  pretty = Doc.text . show

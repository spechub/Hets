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
import qualified Data.Set as S

import CASL.AS_Basic_CASL (SORT, VAR)
import CASL.Sign (emptySign, Sign, sortRel)
import CASL.Morphism (Morphism)
import qualified Common.Doc as Doc
import qualified Common.DocUtils as DocUtils
import Common.Id (Id)
import Common.Lib.Rel (predecessors)

import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)

-- | A process has zero or more parameter sorts, and a communication
-- alphabet.
data ProcProfile = ProcProfile
    { procArgs :: [SORT]
    , procAlphabet :: ProcAlpha
    } deriving (Eq, Show)

-- | A process communication alphabet consists of a set of sort names
-- and typed channel names.
data TypedChanName = TypedChanName CHANNEL_NAME SORT
                     deriving (Eq, Ord, Show)
data CommType = CommTypeSort SORT
              | CommTypeChan TypedChanName
                deriving (Eq, Ord, Show)
type ProcAlpha = S.Set CommType

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map PROCESS_NAME ProcProfile
type ProcVarMap = Map.Map VAR SORT

-- Close a communication alphabet under CASL subsort
closeCspCommAlpha :: CspSign -> ProcAlpha -> ProcAlpha
closeCspCommAlpha sig alpha =
    S.unions $ S.toList $ S.map (closeOneCspComm sig) alpha

-- Close one CommType under CASL subsort
closeOneCspComm :: CspSign -> CommType -> ProcAlpha
closeOneCspComm sig x =
    case x of
      (CommTypeSort s) ->
          S.map CommTypeSort (cspSubsortPreds sig s)
      (CommTypeChan (TypedChanName c s)) ->
          (S.map CommTypeSort (cspSubsortPreds sig s))
          `S.union`
          (S.map (foo c) (cspSubsortPreds sig s))
    where foo c s = CommTypeChan $ TypedChanName c s

-- Get the subsorts of a sort from a CspCASL signature
cspSubsortPreds :: CspSign -> SORT -> S.Set SORT
cspSubsortPreds sig s = S.union preds (S.singleton s)
    where preds = predecessors (sortRel sig) s



{- Will probably be useful, but doesn't appear to be right now.

-- Extract the sorts from a process alphabet
procAlphaSorts :: ProcAlpha -> S.Set SORT
procAlphaSorts a = stripMaybe $ S.map justSort a
    where justSort n = case n of
                         (CommTypeSort s) -> Just s
                         _ -> Nothing
-- Extract the typed channel names from a process alphabet
procAlphaChans :: ProcAlpha -> S.Set TypedChanName
procAlphaChans a = stripMaybe $ S.map justChan a
    where justChan n = case n of
                         (CommTypeChan c) -> Just c
                         _ -> Nothing
-- Given a set of Maybes, filter to keep only the Justs
stripMaybe :: Ord a => S.Set (Maybe a) -> S.Set a
stripMaybe x = S.fromList $ Maybe.catMaybes $ S.toList x

-- Close a set of sorts under a subsort relation
cspSubsortCloseSorts :: CspSign -> S.Set SORT -> S.Set SORT
cspSubsortCloseSorts sig sorts =
    S.unions subsort_sets
        where subsort_sets = S.toList $ S.map (cspSubsortPreds sig) sorts

-}





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

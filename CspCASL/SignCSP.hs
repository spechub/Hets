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

import CASL.AS_Basic_CASL (SORT)
import CASL.Sign (emptySign, Sign, extendedInfo, sortRel)
import CASL.Morphism (Morphism)
import qualified Common.Doc as Doc
import qualified Common.DocUtils as DocUtils
import Common.Id (Id, SIMPLE_ID)
import Common.Lib.Rel (predecessors)

import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)

-- | A process has zero or more parameter sorts, and a communication
-- alphabet.
data ProcProfile = ProcProfile [SORT] CommAlpha
                   deriving (Eq, Show)

-- | A process communication alphabet consists of a set of sort names
-- and typed channel names.
data TypedChanName = TypedChanName CHANNEL_NAME SORT
                     deriving (Eq, Ord, Show)
data CommType = CommTypeSort SORT
              | CommTypeChan TypedChanName
                deriving (Eq, Ord)
instance Show CommType where
    show (CommTypeSort s) = show s
    show (CommTypeChan (TypedChanName c s)) = show (c, s)

type CommAlpha = S.Set CommType

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map PROCESS_NAME ProcProfile
type ProcVarMap = Map.Map SIMPLE_ID SORT

-- Close a communication alphabet under CASL subsort
closeCspCommAlpha :: CspCASLSign -> CommAlpha -> CommAlpha
closeCspCommAlpha sig alpha =
    S.unions $ S.toList $ S.map (closeOneCspComm sig) alpha

-- Close one CommType under CASL subsort
closeOneCspComm :: CspCASLSign -> CommType -> CommAlpha
closeOneCspComm sig x =
    case x of
      (CommTypeSort s) -> S.map CommTypeSort (subsorts s)
      (CommTypeChan (TypedChanName c s)) -> (S.map CommTypeSort (subsorts s))
                                            `S.union`
                                            (S.map (mkTypedChan c) (subsorts s))
    where mkTypedChan c s = CommTypeChan $ TypedChanName c s
          subsorts s' = (S.singleton s') `S.union` predecessors (sortRel sig) s'



{- Will probably be useful, but doesn't appear to be right now.

-- Extract the sorts from a process alphabet
procAlphaSorts :: CommAlpha -> S.Set SORT
procAlphaSorts a = stripMaybe $ S.map justSort a
    where justSort n = case n of
                         (CommTypeSort s) -> Just s
                         _ -> Nothing
-- Extract the typed channel names from a process alphabet
procAlphaChans :: CommAlpha -> S.Set TypedChanName
procAlphaChans a = stripMaybe $ S.map justChan a
    where justChan n = case n of
                         (CommTypeChan c) -> Just c
                         _ -> Nothing
-- Given a set of Maybes, filter to keep only the Justs
stripMaybe :: Ord a => S.Set (Maybe a) -> S.Set a
stripMaybe x = S.fromList $ Maybe.catMaybes $ S.toList x

-- Close a set of sorts under a subsort relation
cspSubsortCloseSorts :: CspCASLSign -> S.Set SORT -> S.Set SORT
cspSubsortCloseSorts sig sorts =
    S.unions subsort_sets
        where subsort_sets = S.toList $ S.map (cspSubsortPreds sig) sorts

-}





-- | CSP process signature.
data CspSign = CspSign
    { chans :: ChanNameMap
    , procSet :: ProcNameMap
    } deriving (Eq, Show)

-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CspCASLSign = Sign () CspSign

ccSig2CASLSign :: CspCASLSign -> Sign () ()
ccSig2CASLSign sigma = sigma { extendedInfo = () }

-- | Empty CspCASL signature.
emptyCspCASLSign :: CspCASLSign
emptyCspCASLSign = emptySign emptyCspSign

-- | Empty CSP process signature.
emptyCspSign :: CspSign
emptyCspSign = CspSign
    { chans = Map.empty
    , procSet = Map.empty
    }

-- | Compute union of two CSP process signatures.
addCspProcSig :: CspSign -> CspSign -> CspSign
addCspProcSig a b =
    a { chans = chans a `Map.union` chans b
      , procSet = procSet a `Map.union` procSet b
      }

-- XXX looks incomplete!
isInclusion :: CspSign -> CspSign -> Bool
isInclusion _ _ = True



-- XXX morphisms between CSP process signatures?

data CspAddMorphism = CspAddMorphism
    { channelMap :: Map.Map Id Id
    , processMap :: Map.Map Id Id
    } deriving (Eq, Show)

type CspMorphism = Morphism () CspSign CspAddMorphism

emptyCspAddMorphism :: CspAddMorphism
emptyCspAddMorphism = CspAddMorphism
  { channelMap = Map.empty -- ???
  , processMap = Map.empty
  }

-- dummy instances, need to be elaborated!
instance DocUtils.Pretty CspSign where
  pretty = Doc.text . show
instance DocUtils.Pretty CspAddMorphism where
  pretty = Doc.text . show

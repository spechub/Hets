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

import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME,
    PROCESS(..), CommAlpha(..), CommType(..), TypedChanName(..))

import CspCASL.AS_CspCASL ()
import CspCASL.CspCASL_Keywords
import CspCASL.Print_CspCASL

import CASL.AS_Basic_CASL (FORMULA, SORT)
import CASL.Sign (emptySign, Sign, extendedInfo, sortRel)
import CASL.Morphism (Morphism)

import Common.AS_Annotation (Named)

import Common.Doc
import Common.DocUtils

import Common.Id (Id, SIMPLE_ID, mkSimpleId, nullRange)
import Common.Lib.Rel (predecessors)
import Common.Result

import Control.Monad (unless)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | A process has zero or more parameter sorts, and a communication
-- alphabet.
data ProcProfile = ProcProfile [SORT] CommAlpha
                   deriving (Eq, Show)

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map PROCESS_NAME ProcProfile
type ProcVarMap = Map.Map SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- Close a communication alphabet under CASL subsort
closeCspCommAlpha :: CspCASLSign -> CommAlpha -> CommAlpha
closeCspCommAlpha sig = Set.unions . Set.toList . Set.map (closeOneCspComm sig)

-- Close one CommType under CASL subsort
closeOneCspComm :: CspCASLSign -> CommType -> CommAlpha
closeOneCspComm sig x = let
  mkTypedChan c s = CommTypeChan $ TypedChanName c s
  subsorts s' = Set.singleton s' `Set.union` predecessors (sortRel sig) s'
  in case x of
    CommTypeSort s -> Set.map CommTypeSort (subsorts s)
    CommTypeChan (TypedChanName c s) -> Set.map CommTypeSort (subsorts s)
      `Set.union` Set.map (mkTypedChan c) (subsorts s)

{- Will probably be useful, but doesn't appear to be right now.

-- Extract the sorts from a process alphabet
procAlphaSorts :: CommAlpha -> Set.Set SORT
procAlphaSorts a = stripMaybe $ Set.map justSort a
    where justSort n = case n of
                         (CommTypeSort s) -> Just s
                         _ -> Nothing
-- Extract the typed channel names from a process alphabet
procAlphaChans :: CommAlpha -> Set.Set TypedChanName
procAlphaChans a = stripMaybe $ Set.map justChan a
    where justChan n = case n of
                         (CommTypeChan c) -> Just c
                         _ -> Nothing
-- Given a set of Maybes, filter to keep only the Justs
stripMaybe :: Ord a => Set.Set (Maybe a) -> Set.Set a
stripMaybe x = Set.fromList $ Maybe.catMaybes $ Set.toList x

-- Close a set of sorts under a subsort relation
cspSubsortCloseSorts :: CspCASLSign -> Set.Set SORT -> Set.Set SORT
cspSubsortCloseSorts sig sorts =
    Set.unions subsort_sets
        where subsort_sets = Set.toList $ Set.map (cspSubsortPreds sig) sorts

-}

-- | CSP process signature.
data CspSign = CspSign
    { chans :: ChanNameMap
    , procSet :: ProcNameMap
    -- | Added for uniformity to the CASL static analysis. After
    --   static analysis this is the empty list.
    , ccSentences :: [Named CspCASLSen]
    } deriving (Eq, Show)

-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CspCASLSign = Sign () CspSign

ccSig2CASLSign :: CspCASLSign -> Sign () ()
ccSig2CASLSign sigma = sigma { extendedInfo = () }

ccSig2CspSign :: CspCASLSign -> CspSign
ccSig2CspSign sigma = extendedInfo sigma

-- | Empty CspCASL signature.
emptyCspCASLSign :: CspCASLSign
emptyCspCASLSign = emptySign emptyCspSign

-- | Empty CSP process signature.
emptyCspSign :: CspSign
emptyCspSign = CspSign
    { chans = Map.empty
    , procSet = Map.empty
    , ccSentences =[]
    }

-- | Compute union of two CSP process signatures.
addCspProcSig :: CspSign -> CspSign -> CspSign
addCspProcSig a b =
    a { chans = chans a `Map.union` chans b
      , procSet = procSet a `Map.union` procSet b
      }

-- | Compute difference of two CSP process signatures.
diffCspProcSig :: CspSign -> CspSign -> CspSign
diffCspProcSig a b =
    a { chans = chans a `Map.difference` chans b
      , procSet = procSet a `Map.difference` procSet b
      }


-- XXX looks incomplete!
isInclusion :: CspSign -> CspSign -> Bool
isInclusion _ _ = True


-- XXX morphisms between CSP process signatures?

data CspAddMorphism = CspAddMorphism
    { channelMap :: Map.Map Id Id
    , processMap :: Map.Map Id Id
    } deriving (Eq, Show)

composeIdMaps :: Map.Map Id Id -> Map.Map Id Id -> Map.Map Id Id
composeIdMaps m1 m2 = Map.foldWithKey (\ i j -> case Map.lookup j m2 of
  Nothing -> error "SignCsp.composeIdMaps"
  Just k -> Map.insert i k) Map.empty m1

composeCspAddMorphism :: CspAddMorphism -> CspAddMorphism
                      -> Result CspAddMorphism
composeCspAddMorphism m1 m2 = return emptyCspAddMorphism
  { channelMap = composeIdMaps (channelMap m1) $ channelMap m2
  , processMap = composeIdMaps (processMap m1) $ processMap m2 }

inverseCspAddMorphism :: CspAddMorphism -> Result CspAddMorphism
inverseCspAddMorphism cm = do
  let chL = Map.toList $ channelMap cm
      prL = Map.toList $ processMap cm
      swap = map $ \ (a, b) -> (b, a)
      isInj l = length l == Set.size (Set.fromList $ map snd l)
  unless (isInj chL) $ fail "invertCspAddMorphism.channelMap"
  unless (isInj prL) $ fail "invertCspAddMorphism.processMap"
  return emptyCspAddMorphism
    { channelMap = Map.fromList $ swap chL
    , processMap = Map.fromList $ swap prL }

type CspMorphism = Morphism () CspSign CspAddMorphism

emptyCspAddMorphism :: CspAddMorphism
emptyCspAddMorphism = CspAddMorphism
  { channelMap = Map.empty -- ???
  , processMap = Map.empty
  }

-- | Pretty printing for CspCASL signatures
instance Pretty CspSign where
  pretty = printCspSign

printCspSign :: CspSign -> Doc
printCspSign sigma =
    chan_part $+$ proc_part
        where chan_part =
                  case (Map.size $ chans sigma) of
                    0 -> empty
                    1 -> (keyword channelS) <+> printChanNameMap (chans sigma)
                    _ -> (keyword channelsS) <+> printChanNameMap (chans sigma)
              proc_part = (keyword processS) <+> printProcNameMap (procSet sigma)

-- | Pretty printing for channel name maps
instance Pretty ChanNameMap where
  pretty = printChanNameMap

printChanNameMap :: ChanNameMap -> Doc
printChanNameMap chanMap =
    vcat $ punctuate semi $ map printChan $ Map.toList chanMap
        where printChan (chanName, sort) =
                  (pretty chanName) <+> colon <+> (pretty sort)

-- | Pretty printing for process name maps
instance Pretty ProcNameMap where
  pretty = printProcNameMap

printProcNameMap :: ProcNameMap -> Doc
printProcNameMap procNameMap =
    vcat $ punctuate semi $ map printProcName $ Map.toList procNameMap
    where printProcName (procName, procProfile) =
              (pretty procName) <+> pretty procProfile

-- | Pretty printing for process profiles
instance Pretty ProcProfile where
  pretty = printProcProfile

printProcProfile :: ProcProfile -> Doc
printProcProfile (ProcProfile sorts commAlpha) =
    printArgs sorts <+> colon <+> (ppWithCommas $ Set.toList commAlpha)
    where printArgs [] = empty
          printArgs args = parens $ ppWithCommas args

-- | Pretty printing for Csp morphisms
instance Pretty CspAddMorphism where
  pretty = text . show

-- Sentences

-- | A CspCASl senetence is either a CASL formula or a Procsses
--   equation. A process equation has on the LHS a process name, a
--   list of parameters which are qualified variables (which are
--   terms), a constituent( or is it permitted ?) communication alphabet and
--   finally on the RHS a fully qualified process.
data CspCASLSen = CASLSen (FORMULA ())
                | ProcessEq PROCESS_NAME ProcVarList CommAlpha PROCESS
                  deriving (Show, Eq, Ord)

instance Pretty CspCASLSen where
    -- Not implemented yet - the pretty printing of the casl sentences
    pretty(CASLSen f) = pretty f
    pretty(ProcessEq pn varList alpha proc) =
        let varDoc = if (null varList)
                     then empty
                     else parens $ sepByCommas $ map pretty (map fst varList)
        in pretty pn <+> varDoc <+> equals <+> pretty proc

emptyCCSen :: CspCASLSen
emptyCCSen =
    let emptyProcName = mkSimpleId "empty"
        emptyVarList = []
        emptyAlphabet = Set.empty
        emptyProc = Skip nullRange
    in ProcessEq emptyProcName emptyVarList emptyAlphabet emptyProc

isCASLSen :: CspCASLSen -> Bool
isCASLSen (CASLSen _) = True
isCASLSen _           = False

isProcessEq :: CspCASLSen -> Bool
isProcessEq (ProcessEq _ _ _ _) = True
isProcessEq _ = False


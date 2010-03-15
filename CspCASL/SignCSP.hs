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
    PROCESS(..), CommAlpha, CommType(..), TypedChanName(..))

import CspCASL.AS_CspCASL ()
import CspCASL.CspCASL_Keywords
import CspCASL.Print_CspCASL ()

import CASL.AS_Basic_CASL (CASLFORMULA, SORT, TERM)
import CASL.Sign (CASLSign, emptySign, Sign, extendedInfo, sortRel)

import Common.AS_Annotation (Named)

import Common.Doc
import Common.DocUtils

import Common.Id
import Common.Lib.Rel (predecessors)

import qualified Data.Map as Map
import qualified Data.Set as Set

-- | A process has zero or more parameter sorts, and a communication
-- alphabet.
data ProcProfile = ProcProfile [SORT] CommAlpha
                   deriving (Eq, Ord, Show)

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map PROCESS_NAME ProcProfile
type ProcVarMap = Map.Map SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- Close a communication alphabet under CASL subsort
closeCspCommAlpha :: CspCASLSign -> CommAlpha -> CommAlpha
closeCspCommAlpha sig =
    Set.unions . Set.toList . Set.map (closeOneCspComm sig)

-- Close one CommType under CASL subsort
closeOneCspComm :: CspCASLSign -> CommType -> CommAlpha
closeOneCspComm sig x = let
  mkTypedChan c s = CommTypeChan $ TypedChanName c s
  subsorts s' =
      Set.singleton s' `Set.union` predecessors (sortRel sig) s'
  in case x of
    CommTypeSort s ->
        Set.map CommTypeSort (subsorts s)
    CommTypeChan (TypedChanName c s) ->
        Set.map CommTypeSort (subsorts s)
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
        where subsort_sets =
                  Set.toList $ Set.map (cspSubsortPreds sig) sorts

-}

-- | CSP process signature.
data CspSign = CspSign
    { chans :: ChanNameMap
    , procSet :: ProcNameMap
    -- | Added for uniformity to the CASL static analysis. After
    -- static analysis this is the empty list.
    , ccSentences :: [Named CspCASLSen]
    } deriving (Eq, Ord, Show)

-- | I dont know if this is implemented correctly. Always prefers sign1 if there
-- are clashes in chans or procSet. BUG?
cspSignUnion :: CspSign -> CspSign -> CspSign
cspSignUnion sign1 sign2 =
    CspSign { chans = Map.union (chans sign1) (chans sign2)
            , procSet = Map.union (procSet sign1) (procSet sign2)
            , ccSentences = ccSentences sign1 ++ ccSentences sign2
            }
-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CspCASLSign = Sign () CspSign

ccSig2CASLSign :: CspCASLSign -> CASLSign
ccSig2CASLSign sigma = sigma { extendedInfo = () }

-- | Projection from CspCASL signature to Csp signature
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
    CspSign { chans = chans a `Map.union` chans b
            , procSet = procSet a `Map.union` procSet b
            , ccSentences = ccSentences a ++ ccSentences b
      }

-- | Compute difference of two CSP process signatures.
diffCspProcSig :: CspSign -> CspSign -> CspSign
diffCspProcSig a b =
    CspSign { chans = chans a `Map.difference` chans b
            , procSet = procSet a `Map.difference` procSet b
            }

-- | Is one Csp Signature a sub signature of another
isCspSubSign :: CspSign -> CspSign -> Bool
isCspSubSign a b =
    chans a `Map.isSubmapOf` chans b &&
    procSet a `Map.isSubmapOf` procSet b


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
              proc_part = (keyword processS) <+>
                          printProcNameMap (procSet sigma)

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

-- Sentences

-- | FQProcVarList should only contain fully qualified CASL variables which are
-- | TERMs i.e. constructed via the TERM constructor Qual_var.
type FQProcVarList = [TERM ()]

-- | A CspCASl senetence is either a CASL formula or a Procsses equation. A
-- | process equation has on the LHS a process name, a list of parameters which
-- | are qualified variables (which are terms), a constituent( or is it
-- | permitted ?) communication alphabet and finally on the RHS a fully
-- | qualified process.
data CspCASLSen
    = CASLSen (CASLFORMULA)
    | ProcessEq PROCESS_NAME FQProcVarList CommAlpha PROCESS
      deriving (Show, Eq, Ord)

instance GetRange CspCASLSen

instance Pretty CspCASLSen where
    pretty(CASLSen f) = pretty f
    pretty(ProcessEq pn varList commAlpha proc) =
        let varDoc = if (null varList)
                     then empty
                     else parens $ sepByCommas $ map pretty varList
            commAlphaDoc = brackets ((text "CommAlpha:") <+>
                                     (text $ show commAlpha))
        in pretty pn <+> varDoc <+> commAlphaDoc <+>
           equals <+> pretty proc

-- | Empty CspCASL sentence
emptyCCSen :: CspCASLSen
emptyCCSen =
    let emptyProcName = mkSimpleId "empty"
        emptyVarList = []
        emptyAlphabet = Set.empty
        emptyProc = Skip nullRange
    -- BUG - this is incorrect
    in ProcessEq emptyProcName emptyVarList emptyAlphabet emptyProc

-- | Test if a CspCASL sentence is a CASL sentence
isCASLSen :: CspCASLSen -> Bool
isCASLSen (CASLSen _) = True
isCASLSen _ = False

-- | Test if a CspCASL sentence is a Process Equation.
isProcessEq :: CspCASLSen -> Bool
isProcessEq (ProcessEq _ _ _ _) = True
isProcessEq _ = False

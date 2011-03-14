{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  $Id$
Description :  CspCASL signatures
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

signatures for CSP-CASL
-}

module CspCASL.SignCSP where

import CASL.AS_Basic_CASL (CASLFORMULA, SORT, TERM)
import CASL.Sign (uniteCASLSign, CASLSign, emptySign, Sign(..), extendedInfo,
                  sortRel, isSubSig)
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, SIMPLE_PROCESS_NAME,
                                   FQ_PROCESS_NAME, PROCESS (..),
                                   CommAlpha, CommType (..), TypedChanName (..))
import CspCASL.AS_CspCASL ()
import CspCASL.AS_CspCASL_Process (ProcProfile (..))
import CspCASL.CspCASL_Keywords
import qualified CspCASL.LocalTop as LocalTop
import CspCASL.Print_CspCASL ()
import Common.AS_Annotation (Named)
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Lib.Rel (Rel, predecessors)
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set

type ChanNameMap = Map.Map CHANNEL_NAME SORT
type ProcNameMap = Map.Map SIMPLE_PROCESS_NAME (Set.Set ProcProfile)
type ProcVarMap = Map.Map SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- | Add a process name and its profile to a process name map.  exist.
addProcNameToProcNameMap :: SIMPLE_PROCESS_NAME -> ProcProfile ->
                            ProcNameMap -> ProcNameMap
addProcNameToProcNameMap name profile pm =
    let l = Map.findWithDefault Set.empty name pm
    in Map.insert name (Set.insert profile l) pm

-- | Test if a simple process name with a profile is in the process name map.
isNameInProcNameMap :: SIMPLE_PROCESS_NAME -> ProcProfile -> ProcNameMap -> Bool
isNameInProcNameMap name profile pm =
  let l = Map.findWithDefault Set.empty name pm
  in Set.member profile l

-- | Given a simple process name and a required number of parameters, find a
-- unqiue profile with that many parameters if possible. If this is not possible
-- (i.e., name does not exist, or no profile with the required number of
-- arguments or not unique profile for the required number of arguments), then
-- the functions returns a failed result with a helpful error message.  failure.
getUniqueProfileInProcNameMap :: SIMPLE_PROCESS_NAME -> Int -> ProcNameMap ->
                                 Result ProcProfile
getUniqueProfileInProcNameMap name numParams pm =
  let profiles = Map.findWithDefault Set.empty name pm
      isMatch (ProcProfile argSorts _) =
        length(argSorts) == numParams
      matchedProfiles = Set.filter isMatch profiles
  in if Set.null matchedProfiles
     then -- No matches
            mkError ("Process name not in signature with "
            ++ show numParams ++ " parameters:") name
     else if Set.size(matchedProfiles) > 1
          then -- too many matches
            mkError ("Process name not unique in signature with "
            ++ show numParams ++ " parameters:") name
          else -- unique profile
            Result [] $ Just $ (Set.toList matchedProfiles)!!0

-- | Close a proc name map under a sub-sort relation. Assumes all the proc
-- profile's comms are in the sub sort relation and simply makes the comms
-- downward closed under the sub-sort relation.
closeProcNameMapSortRel :: Rel SORT -> ProcNameMap -> ProcNameMap
closeProcNameMapSortRel sig pm =
  Map.map (Set.map $ closeProcProfileSortRel sig) pm

-- | Close a profile under a sub-sort relation.  Assumes the proc profile's
-- comms are in the sub sort relation and simply makes the comms downward closed
-- under the sub-sort relation.
closeProcProfileSortRel :: Rel SORT -> ProcProfile -> ProcProfile
closeProcProfileSortRel sig (ProcProfile argSorts comms) =
  ProcProfile argSorts (closeCspCommAlpha sig comms)

-- Close a communication alphabet under CASL subsort
closeCspCommAlpha :: Rel SORT -> CommAlpha -> CommAlpha
closeCspCommAlpha sr =
    Set.unions . Set.toList . Set.map (closeOneCspComm sr)

-- Close one CommType under CASL subsort
closeOneCspComm :: Rel SORT -> CommType -> CommAlpha
closeOneCspComm sr x = let
  mkTypedChan c s = CommTypeChan $ TypedChanName c s
  subsorts s' =
      Set.singleton s' `Set.union` predecessors sr s'
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
-- are clashes in chans or procSet. BUG? I guess this would be called once the
-- union of the data signatures has been computed. But this unioned data
-- signature may have changed the subsort structure, so the process map may have
-- to ben repaired to make the keys closed under subsort.
cspSignUnion :: CspSign -> CspSign -> CspSign
cspSignUnion _ _ = error "NYI: CspCASL.SignCSP.cspSignUnion"
    -- CspSign { chans = Map.union (chans sign1) (chans sign2)
    --         , procSet = Map.union (procSet sign1) (procSet sign2)
    --         , ccSentences = ccSentences sign1 ++ ccSentences sign2
    --         }

-- | A CspCASL signature is a CASL signature with a CSP process
-- signature in the extendedInfo part.
type CspCASLSign = Sign () CspSign

ccSig2CASLSign :: CspCASLSign -> CASLSign
ccSig2CASLSign sigma = sigma { extendedInfo = () }

-- | Projection from CspCASL signature to Csp signature
ccSig2CspSign :: CspCASLSign -> CspSign
ccSig2CspSign = extendedInfo

-- | Empty CspCASL signature.
emptyCspCASLSign :: CspCASLSign
emptyCspCASLSign = emptySign emptyCspSign

-- | Empty CSP process signature.
emptyCspSign :: CspSign
emptyCspSign = CspSign
    { chans = Map.empty
    , procSet = Map.empty
    , ccSentences = []
    }

-- | Compute union of two CSP CASL signatures.
unionCspCASLSign :: CspCASLSign -> CspCASLSign -> Result CspCASLSign
unionCspCASLSign s1 s2 = do
  -- Compute the unioned data signature ignoring the csp signatures
  let newDataSig = uniteCASLSign (ccSig2CASLSign s1) (ccSig2CASLSign s2)
  -- Check that the new data signature has local top elements
  let diags' = LocalTop.checkLocalTops $ sortRel newDataSig
  -- Compute the unioned csp signature with respect to the new data signature
  let newCspSign = unionCspSign newDataSig (extendedInfo s1) (extendedInfo s2)
  -- Only error will be added if there are any probelms. If there are no
  -- problems no errors will be added and hets will continue as normal.
  appendDiags (diags')
  -- put both the new data signature and the csp signature back together
  return $ newDataSig {extendedInfo = newCspSign}

-- | Compute union of two CSP signatures assuming the new already computed data
-- signature.
unionCspSign :: Sign () () -> CspSign -> CspSign -> CspSign
unionCspSign dataSig a b =
  let sr = sortRel dataSig
      closedProcSetA = closeProcNameMapSortRel sr $ procSet a
      closedProcSetB = closeProcNameMapSortRel sr $ procSet b
  in emptyCspSign
    { chans = chans a `Map.union` chans b
      -- Union the maps, and where there is the same key in both maps take the
      -- union of both of the process name sets for that key.
    , procSet = Map.unionWith Set.union closedProcSetA closedProcSetB
    }



-- | Compute difference of two CSP process signatures.
diffCspProcSig :: CspSign -> CspSign -> CspSign
diffCspProcSig a b = emptyCspSign
  { chans = chans a `Map.difference` chans b
  , procSet = procSet a `Map.difference` procSet b
  }

-- | Is one CspCASL Signature a sub signature of another
isCspCASLSubSig :: CspCASLSign -> CspCASLSign -> Bool
isCspCASLSubSig a b =
  -- Normal casl subsignature and our extended csp part
  isSubSig isCspSubSign a b &&
  -- but also the sorts and sub-sort rels must be equal. If they are not then we
  -- cant just add the processes in as their profiles need to be donward closed
  -- under the new sort-rels
  sortSet a == sortSet a &&
  sortRel a == sortRel a

-- | Is one Csp Signature a sub signature of another assuming the same data
-- signature for now.
isCspSubSign :: CspSign -> CspSign -> Bool
isCspSubSign a b =
    chans a `Map.isSubmapOf` chans b &&
    -- Check for each profile that the set of names are included.
    Map.isSubmapOfBy (Set.isSubsetOf) (procSet a)  (procSet b)

-- | Pretty printing for CspCASL signatures
instance Pretty CspSign where
  pretty = printCspSign

printCspSign :: CspSign -> Doc
printCspSign sigma =
    chan_part $+$ proc_part
        where chan_part =
                  case Map.size $ chans sigma of
                    0 -> empty
                    s -> keyword (if s > 1 then channelsS else channelS)
                         <+> printChanNameMap (chans sigma)
              proc_part = keyword processS <+>
                          printProcNameMap (procSet sigma)

-- | Pretty printing for channel name maps
instance Pretty ChanNameMap where
  pretty = printChanNameMap

printChanNameMap :: ChanNameMap -> Doc
printChanNameMap chanMap =
    vcat $ punctuate semi $ map printChan $ Map.toList chanMap
        where printChan (chanName, sort) =
                  pretty chanName <+> colon <+> pretty sort

-- | Pretty printing for process name maps
instance Pretty ProcNameMap where
  pretty = printProcNameMap

printProcNameMap :: ProcNameMap -> Doc
printProcNameMap procNameMap =
    vcat $ punctuate semi $ concatMap printProcName $ Map.toList procNameMap
    where printProcName (procName, procProfileSet) =
            map (\procProfile -> pretty procName <+>
                                 pretty procProfile) $ Set.toList procProfileSet

-- | Pretty printing for process profiles
instance Pretty ProcProfile where
  pretty = printProcProfile

printProcProfile :: ProcProfile -> Doc
printProcProfile (ProcProfile sorts commAlpha) =
    printArgs sorts <+> colon <+> ppWithCommas (Set.toList commAlpha)
    where printArgs [] = empty
          printArgs args = parens $ ppWithCommas args

-- Sentences

-- | FQProcVarList should only contain fully qualified CASL variables which are
-- TERMs i.e. constructed via the TERM constructor Qual_var.
type FQProcVarList = [TERM ()]

-- | A CspCASl senetence is either a CASL formula or a Procsses equation. A
-- process equation has on the LHS a process name, a list of parameters which
-- are qualified variables (which are terms), a constituent( or is it permitted
-- ?) communication alphabet and finally on the RHS a fully qualified process.
data CspCASLSen
    = CASLSen (CASLFORMULA)
    | ProcessEq FQ_PROCESS_NAME FQProcVarList CommAlpha PROCESS
      deriving (Show, Eq, Ord)

instance GetRange CspCASLSen

instance Pretty CspCASLSen where
    pretty (CASLSen f) = pretty f
    pretty (ProcessEq pn varList _commAlpha proc) =
        let varDoc = if null varList
                     then empty
                     else parens $ ppWithCommas varList
        in pretty pn <+> varDoc <+> equals <+> pretty proc

-- | Empty CspCASL sentence
emptyCCSen :: CspCASLSen
emptyCCSen =
    -- let emptyProcName = mkSimpleId "empty"
    --     emptyVarList = []
    --     emptyAlphabet = Set.empty
    --     emptyProc = Skip nullRange
    -- BUG - this is incorrect
    --in
  error "Error in CspCASL.SignCSP.emptyCCSen: NYI"
       -- ProcessEq emptyProcName emptyVarList emptyAlphabet emptyProc

-- | Test if a CspCASL sentence is a CASL sentence
isCASLSen :: CspCASLSen -> Bool
isCASLSen (CASLSen _) = True
isCASLSen _ = False

-- | Test if a CspCASL sentence is a Process Equation.
isProcessEq :: CspCASLSen -> Bool
isProcessEq (ProcessEq _ _ _ _) = True
isProcessEq _ = False

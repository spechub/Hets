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

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.ToDoc
import CspCASL.AS_CspCASL_Process
         (CHANNEL_NAME, PROCESS_NAME, FQ_PROCESS_NAME, PROCESS (..),
          CommAlpha, CommType (..), TypedChanName (..), ProcProfile (..))
import CspCASL.AS_CspCASL ()
import CspCASL.CspCASL_Keywords
import qualified CspCASL.LocalTop as LocalTop
import CspCASL.Print_CspCASL ()
import Common.AS_Annotation (Named)
import Common.AnnoState
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Lib.Rel (Rel, predecessors)
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set

type ChanNameMap = Map.Map CHANNEL_NAME (Set.Set SORT)
type ProcNameMap = Map.Map PROCESS_NAME (Set.Set ProcProfile)
type ProcVarMap = Map.Map SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- | Add a process name and its profile to a process name map.  exist.
addProcNameToProcNameMap :: PROCESS_NAME -> ProcProfile ->
                            ProcNameMap -> ProcNameMap
addProcNameToProcNameMap name profile pm =
    let l = Map.findWithDefault Set.empty name pm
    in Map.insert name (Set.insert profile l) pm

-- | Test if a simple process name with a profile is in the process name map.
isNameInProcNameMap :: PROCESS_NAME -> ProcProfile -> ProcNameMap -> Bool
isNameInProcNameMap name profile pm =
  let l = Map.findWithDefault Set.empty name pm
  in Set.member profile l

{- | Given a simple process name and a required number of parameters, find a
unqiue profile with that many parameters if possible. If this is not possible
(i.e., name does not exist, or no profile with the required number of
arguments or not unique profile for the required number of arguments), then
the functions returns a failed result with a helpful error message.  failure. -}
getUniqueProfileInProcNameMap :: PROCESS_NAME -> Int -> ProcNameMap ->
                                 Result ProcProfile
getUniqueProfileInProcNameMap name numParams pm =
  let profiles = Map.findWithDefault Set.empty name pm
      isMatch (ProcProfile argSorts _) =
        length argSorts == numParams
      matchedProfiles = Set.filter isMatch profiles
  in case Set.toList matchedProfiles of
       [] -> mkError ("Process name not in signature with "
             ++ show numParams ++ " parameters:") name
       [p] -> return p
       _ -> mkError ("Process name not unique in signature with "
            ++ show numParams ++ " parameters:") name

closeProcs :: Rel SORT -> CspSign -> CspSign
closeProcs r s = s { procSet = closeProcNameMapSortRel r $ procSet s }

{- | Close a proc name map under a sub-sort relation. Assumes all the proc
profile's comms are in the sub sort relation and simply makes the comms
downward closed under the sub-sort relation. -}
closeProcNameMapSortRel :: Rel SORT -> ProcNameMap -> ProcNameMap
closeProcNameMapSortRel sig =
  Map.map (Set.map $ closeProcProfileSortRel sig)

{- | Close a profile under a sub-sort relation.  Assumes the proc profile's
comms are in the sub sort relation and simply makes the comms downward closed
under the sub-sort relation. -}
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
    {- | Added for uniformity to the CASL static analysis. After
    static analysis this is the empty list. -}
    , ccSentences :: [Named CspCASLSen]
    } deriving (Eq, Ord, Show)

-- | plain union
cspSignUnion :: CspSign -> CspSign -> CspSign
cspSignUnion sign1 sign2 = emptyCspSign
    { chans = addMapSet (chans sign1) (chans sign2)
    , procSet = addMapSet (procSet sign1) (procSet sign2) }

{- | A CspCASL signature is a CASL signature with a CSP process
signature in the extendedInfo part. -}
type CspCASLSign = Sign CspSen CspSign

ccSig2CASLSign :: CspCASLSign -> CASLSign
ccSig2CASLSign sigma = sigma { extendedInfo = (), sentences = [] }

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
  let newDataSig = addSig (\ _ _ -> emptyCspSign) s1 s2
  -- Check that the new data signature has local top elements
      rel = sortRel newDataSig
      diags' = LocalTop.checkLocalTops rel
  -- Compute the unioned csp signature with respect to the new data signature
      newCspSign = unionCspSign rel (extendedInfo s1) (extendedInfo s2)
  {- Only error will be added if there are any probelms. If there are no
  problems no errors will be added and hets will continue as normal. -}
  appendDiags diags'
  -- put both the new data signature and the csp signature back together
  return $ newDataSig {extendedInfo = newCspSign}

{- | Compute union of two CSP signatures assuming the new already computed data
signature. -}
unionCspSign :: Rel SORT -> CspSign -> CspSign -> CspSign
unionCspSign sr a b = cspSignUnion (closeProcs sr a) (closeProcs sr b)

-- | Compute difference of two CSP process signatures.
diffCspSig :: CspSign -> CspSign -> CspSign
diffCspSig a b = emptyCspSign
  { chans = diffMapSet (chans a) $ chans b
  , procSet = diffMapSet (procSet a) $ procSet b
  }

-- | Is one CspCASL Signature a sub signature of another
isCspCASLSubSig :: CspCASLSign -> CspCASLSign -> Bool
isCspCASLSubSig =
  -- Normal casl subsignature and our extended csp part
  isSubSig isCspSubSign
  {- Also the sorts and sub-sort rels should be equal. If they are not then we
  cannot just add the processes in as their profiles need to be donward closed
  under the new sort-rels, but we do not check this here. -}

{- | Is one Csp Signature a sub signature of another assuming the same data
signature for now. -}
isCspSubSign :: CspSign -> CspSign -> Bool
isCspSubSign a b =
    isSubMapSet (chans a) (chans b) &&
    -- Check for each profile that the set of names are included.
    isSubMapSet (procSet a) (procSet b)

-- | Pretty printing for CspCASL signatures
instance Pretty CspSign where
  pretty = printCspSign

mapSetToList :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> [(a, b)]
mapSetToList = concatMap (\ (c, ts) -> map (\ t -> (c, t)) $ Set.toList ts)
  . Map.toList

printCspSign :: CspSign -> Doc
printCspSign sigma =
    case mapSetToList $ chans sigma of
      [] -> empty
      s -> keyword (channelS ++ appendS s) <+> printChanList s
    $+$ case mapSetToList $ procSet sigma of
      [] -> empty
      ps -> keyword processS <+> printProcList ps

-- | Pretty printing for channels
printChanList :: [(CHANNEL_NAME, SORT)] -> Doc
printChanList =
    vcat . punctuate semi . map printChan
        where printChan (chanName, sort) =
                  pretty chanName <+> colon <+> pretty sort

-- | Pretty printing for processes
printProcList :: [(PROCESS_NAME, ProcProfile)] -> Doc
printProcList =
    vcat . punctuate semi . map printProc
    where printProc (procName, procProfile) = pretty procName <+>
                                 pretty procProfile

-- Sentences

{- | FQProcVarList should only contain fully qualified CASL variables which are
TERMs i.e. constructed via the TERM constructor Qual_var. -}
type FQProcVarList = [TERM ()]

{- | A CspCASl senetence is either a CASL formula or a Procsses equation. A
process equation has on the LHS a process name, a list of parameters which
are qualified variables (which are terms), a constituent( or is it permitted
?) communication alphabet and finally on the RHS a fully qualified process. -}
data CspSen = ProcessEq FQ_PROCESS_NAME FQProcVarList CommAlpha PROCESS
      deriving (Show, Eq, Ord)

type CspCASLSen = FORMULA CspSen

instance GetRange CspSen

instance Pretty CspSen where
    pretty (ProcessEq pn varList _commAlpha proc) =
        let varDoc = if null varList
                     then empty
                     else parens $ ppWithCommas varList
        in pretty pn <+> varDoc <+> equals <+> pretty proc

instance FormExtension CspSen
instance TermExtension CspSen
instance TermParser CspSen

isProcessEq :: CspCASLSen -> Bool
isProcessEq f = case f of
   ExtFORMULA _ -> True
   _ -> False

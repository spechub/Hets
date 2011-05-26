{- |
Module      :  $Header$
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
import CASL.Overload
import CASL.Sign
import CASL.ToDoc
import CspCASL.AS_CspCASL_Process
import CspCASL.AS_CspCASL ()
import CspCASL.CspCASL_Keywords
import qualified CspCASL.LocalTop as LocalTop
import CspCASL.Print_CspCASL ()
import Common.AnnoState
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Lib.Rel (Rel, predecessors)
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Ord

type ChanNameMap = Map.Map CHANNEL_NAME (Set.Set SORT)
type ProcNameMap = Map.Map PROCESS_NAME (Set.Set ProcProfile)
type ProcVarMap = Map.Map SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- | Add a process name and its profile to a process name map.  exist.
addProcNameToProcNameMap :: PROCESS_NAME -> ProcProfile -> ProcNameMap
  -> ProcNameMap
addProcNameToProcNameMap name profile =
    Map.insertWith Set.union name (Set.singleton profile)

-- | Test if a simple process name with a profile is in the process name map.
isNameInProcNameMap :: PROCESS_NAME -> ProcProfile -> ProcNameMap -> Bool
isNameInProcNameMap name profile =
  Set.member profile . Map.findWithDefault Set.empty name

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
  subsorts s' = Set.insert s' $ predecessors sr s'
  in case x of
    CommTypeSort s ->
        Set.map CommTypeSort (subsorts s)
    CommTypeChan (TypedChanName c s) ->
        Set.map CommTypeSort (subsorts s)
      `Set.union` Set.map (mkTypedChan c) (subsorts s)

-- | CSP process signature.
data CspSign = CspSign
    { chans :: ChanNameMap
    , procSet :: ProcNameMap
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
    , procSet = Map.empty }

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
printChanList l = let
  gl = groupBy (\ (_, s1) (_, s2) -> s1 == s2) $ sortBy (comparing snd) l
  printChan cl = case cl of
    [] -> empty -- should not happen
    (_, s) : _ -> fsep [ppWithCommas (map fst cl), colon <+> pretty s]
  in sepBySemis $ map printChan gl

-- | Pretty printing for processes
printProcList :: [(PROCESS_NAME, ProcProfile)] -> Doc
printProcList = sepBySemis . map
  (\ (procName, procProfile) -> pretty procName <+> pretty procProfile)

-- * overload relations

relatedSorts :: CspCASLSign -> SORT -> SORT -> Bool
relatedSorts sig s1 s2 = haveCommonSupersorts True sig s1 s2
  || haveCommonSupersorts False sig s1 s2

relatedCommTypes :: CspCASLSign -> CommType -> CommType -> Bool
relatedCommTypes sig ct1 ct2 = case (ct1, ct2) of
  (CommTypeSort s1, CommTypeSort s2) -> relatedSorts sig s1 s2
  (CommTypeChan (TypedChanName c1 s1), CommTypeChan (TypedChanName c2 s2))
    -> c1 == c2 && relatedSorts sig s1 s2
  _ -> False

relatedCommAlpha :: CspCASLSign -> CommAlpha -> CommAlpha -> Bool
relatedCommAlpha sig al1 al2 = Set.null al1 || Set.null al2 ||
  any (\ a -> any (relatedCommTypes sig a) $ Set.toList al1) (Set.toList al2)

relatedProcs :: CspCASLSign -> ProcProfile -> ProcProfile -> Bool
relatedProcs sig (ProcProfile l1 al1) (ProcProfile l2 al2) =
  length l1 == length l2 &&
    and (zipWith (relatedSorts sig) l1 l2)
    && relatedCommAlpha sig al1 al2

-- * Sentences

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
        in fsep [pretty pn, varDoc, equals <+> pretty proc]

instance FormExtension CspSen where
  prefixExt (ProcessEq pn _ _ _) = case pn of
    PROCESS_NAME _ -> (keyword processS <+>)
    FQ_PROCESS_NAME {} -> id

instance TermExtension CspSen
instance TermParser CspSen

isProcessEq :: CspCASLSen -> Bool
isProcessEq f = case f of
   ExtFORMULA _ -> True
   _ -> False

{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CspCASL/SignCSP.hs
Description :  CspCASL signatures
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

signatures for CSP-CASL
-}

module CspCASL.SignCSP
  ( addProcNameToProcNameMap
  , ccSig2CASLSign
  , ccSig2CspSign
  , ChanNameMap
  , closeCspCommAlpha
  , CspCASLSign
  , CspCASLSen
  , CspSen (..)
  , CspSign (..)
  , cspSignUnion
  , diffCspSig
  , emptyCspCASLSign
  , emptyCspSign
  , FQProcVarList
  , getUniqueProfileInProcNameMap
  , isCspCASLSubSig
  , isCspSubSign
  , isNameInProcNameMap
  , isProcessEq
  , ProcNameMap
  , ProcVarList
  , ProcVarMap
  , reduceProcProfile
  , commType2Sort
  , relatedSorts
  , relatedProcs
  , unionCspCASLSign
  ) where

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
import Common.Result
import Common.Lib.Rel (Rel, predecessors, member)
import qualified Common.Lib.MapSet as MapSet
import Common.Utils (keepMins)

import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set
import Data.Data
import Data.List
import Data.Ord

import GHC.Generics (Generic)
import Data.Hashable

type ChanNameMap = MapSet.MapSet CHANNEL_NAME SORT
type ProcNameMap = MapSet.MapSet PROCESS_NAME ProcProfile
type ProcVarMap = Map.HashMap SIMPLE_ID SORT
type ProcVarList = [(SIMPLE_ID, SORT)]

-- | Add a process name and its profile to a process name map.  exist.
addProcNameToProcNameMap :: PROCESS_NAME -> ProcProfile -> ProcNameMap
  -> ProcNameMap
addProcNameToProcNameMap = MapSet.insert

-- | Test if a simple process name with a profile is in the process name map.
isNameInProcNameMap :: PROCESS_NAME -> ProcProfile -> ProcNameMap -> Bool
isNameInProcNameMap = MapSet.member

{- | Given a simple process name and a required number of parameters, find a
unqiue profile with that many parameters if possible. If this is not possible
(i.e., name does not exist, or no profile with the required number of
arguments or not unique profile for the required number of arguments), then
the functions returns a failed result with a helpful error message.  failure. -}
getUniqueProfileInProcNameMap :: PROCESS_NAME -> Int -> ProcNameMap ->
                                 Result ProcProfile
getUniqueProfileInProcNameMap name numParams pm =
  let profiles = MapSet.lookup name pm
      isMatch (ProcProfile argSorts _) =
        length argSorts == numParams
      matchedProfiles = Set.filter isMatch profiles
  in case Set.toList matchedProfiles of
       [] -> mkError ("Process name not in signature with "
             ++ show numParams ++ " parameters:") name
       [p] -> return p
       _ -> mkError ("Process name not unique in signature with "
            ++ show numParams ++ " parameters:") name

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

{- | Remove the implicit sorts from the proc name map under a sub-sort
relation. Assumes all the proc profile's comms are in the sub sort relation and
simply makes the comms contain only the minimal super sorts under the sub-sort
relation. -}
reduceProcNamesInSig :: Rel SORT -> CspSign -> CspSign
reduceProcNamesInSig sr cspSig =
  cspSig { procSet = reduceProcNameMap sr $ procSet cspSig }

{- | Remove the implicit sorts from a proc name map under a sub-sort
relation. Assumes all the proc profile's comms are in the sub sort relation and
simply makes the comms contain only the minimal super sorts under the sub-sort
relation. -}
reduceProcNameMap :: Rel SORT -> ProcNameMap -> ProcNameMap
reduceProcNameMap sr =
  MapSet.map (reduceProcProfile sr)

{- | Remove the implicit sorts from a profile under a sub-sort relation. Assumes
all the proc profile's comms are in the sub sort relation and simply makes the
comms contain only the minimal super sorts under the sub-sort relation. -}
reduceProcProfile :: Rel SORT -> ProcProfile -> ProcProfile
reduceProcProfile sr (ProcProfile argSorts comms) =
  ProcProfile argSorts (reduceCspCommAlpha sr comms)

{- | Remove the implicit sorts from a CommAlpha under a sub-sort
relation. Assumes all the proc profile's comms are in the sub sort relation and
simply makes the comms contain only the minimal super sorts under the sub-sort
relation. -}
reduceCspCommAlpha :: Rel SORT -> CommAlpha -> CommAlpha
reduceCspCommAlpha sr =
  Set.fromList .
    concatMap (keepMins $ cmpCommType sr) . groupBy sameChan . Set.toList

cmpCommType :: Rel SORT -> CommType -> CommType -> Bool
cmpCommType rel t1 t2 = let
  s1 = commType2Sort t1
  s2 = commType2Sort t2
  in s1 == s2 || member s2 s1 rel

commType2Sort :: CommType -> SORT
commType2Sort c = case c of
  CommTypeSort s -> s
  CommTypeChan (TypedChanName _ s) -> s

sameChan :: CommType -> CommType -> Bool
sameChan t1 t2 = case (t1, t2) of
  (CommTypeSort _, CommTypeSort _) -> True
  (CommTypeChan (TypedChanName c1 _), CommTypeChan (TypedChanName c2 _))
      -> c1 == c2
  _ -> False

-- | CSP process signature.
data CspSign = CspSign
    { chans :: ChanNameMap
    , procSet :: ProcNameMap
    } deriving (Show, Eq, Ord, Typeable, Data)

-- | plain union
cspSignUnion :: CspSign -> CspSign -> CspSign
cspSignUnion sign1 sign2 = emptyCspSign
    { chans = chans sign1 `MapSet.union` chans sign2
    , procSet = procSet sign1 `MapSet.union` procSet sign2 }

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
    { chans = MapSet.empty
    , procSet = MapSet.empty }

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
unionCspSign sr a b = reduceProcNamesInSig sr $ cspSignUnion a b

-- | Compute difference of two CSP process signatures.
diffCspSig :: CspSign -> CspSign -> CspSign
diffCspSig a b = emptyCspSign
  { chans = MapSet.difference (chans a) $ chans b
  , procSet = MapSet.difference (procSet a) $ procSet b
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
     MapSet.isSubmapOf (chans a) (chans b) &&
    -- Check for each profile that the set of names are included.
    MapSet.isSubmapOf (procSet a) (procSet b)

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

-- * overload relations: We do not have one of these yet in theory

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
      deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable CspSen

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

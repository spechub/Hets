{- |
Module      :  $Header$
Description :  Symbols and signature morphisms for the CspCASL logic
Copyright   :  (c) Liam O'Reilly, Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Symbols and signature morphisms for the CspCASL logic
-}

module CspCASL.Morphism
    ( CspMorphism
    , CspAddMorphism(..)
    , emptyCspAddMorphism
    , makeChannelNameSymbol
    , makeProcNameSymbol
    , mapSen
    , CspCASL.Morphism.symOf
    , inducedCspSign
    ) where

import CASL.AS_Basic_CASL (FORMULA, TERM)
import CASL.Sign as CASL_Sign
import CASL.Morphism as CASL_Morphism
import qualified CASL.MapSentence as CASL_MapSen

import Common.Doc
import Common.DocUtils
import Common.Id(simpleIdToId)
import Common.Result(Result)

import Control.Monad (unless)

import CspCASL.AS_CspCASL_Process
import CspCASL.SignCSP
import CspCASL.CspCASL_Keywords

import qualified Data.Map as Map
import qualified Data.Set as Set

-- Symbols

channelNameSymbType :: SymbType
channelNameSymbType = OtherTypeKind channelS

processNameSymbType :: SymbType
processNameSymbType = OtherTypeKind processS

-- | Calculate the set of symbols for a CspCASL signature
symOf :: CspCASLSign -> Set.Set Symbol
symOf sigma =
    let caslSymbols = CASL_Morphism.symOf sigma -- Get CASL symbols
        cspExt = extendedInfo sigma
        chanNames = Map.keysSet (chans cspExt) -- Get the channel names
        procNames = Map.keysSet (procSet cspExt) -- Get the process names
        -- Make channel symbols from names
        chanNameSymbols = Set.map makeChannelNameSymbol chanNames
        -- Make process name symbols from names
        procNameSymbols = Set.map makeProcNameSymbol procNames
    in Set.unions [caslSymbols, chanNameSymbols, procNameSymbols]

-- | Make a symbol form a channel name
makeChannelNameSymbol :: CHANNEL_NAME -> Symbol
makeChannelNameSymbol c =
    Symbol {symName = simpleIdToId c, symbType = channelNameSymbType}

-- | Make a symbol form a process name
makeProcNameSymbol :: PROCESS_NAME -> Symbol
makeProcNameSymbol p =
    Symbol {symName = simpleIdToId p, symbType = processNameSymbType}

-- Morphisms

-- | CspMorphism - This is just the extended part
data CspAddMorphism = CspAddMorphism
    { channelMap :: Map.Map CHANNEL_NAME CHANNEL_NAME
    , processMap :: Map.Map PROCESS_NAME PROCESS_NAME
    } deriving (Eq, Ord, Show)

-- | Compose two Maps. We use this for Composing the channel and
--   process maps of a CspAddMorphism.
composeMaps :: (Ord a, Ord b) => Map.Map a b -> Map.Map b c ->
               Map.Map a c
composeMaps m1 m2 =
    Map.foldWithKey (\ i j -> case Map.lookup j m2 of
                                Nothing -> error "SignCsp.composeMaps"
                                Just k -> Map.insert i k) Map.empty m1

-- | Compose two CspAddMorphisms
composeCspAddMorphism :: CspAddMorphism -> CspAddMorphism
                      -> Result CspAddMorphism
composeCspAddMorphism m1 m2 = return emptyCspAddMorphism
  { channelMap = composeMaps (channelMap m1) $ channelMap m2
  , processMap = composeMaps (processMap m1) $ processMap m2 }

-- | Calculate the inverse of a CspAddMorphism
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

-- | A CspMorphism is a CASL Morphism with the extended_map to be a
--   CspAddMorphism.
type CspMorphism = CASL_Morphism.Morphism () CspSign CspAddMorphism

-- | The empty CspAddMorphism.
emptyCspAddMorphism :: CspAddMorphism
emptyCspAddMorphism =
    -- Note that when applying the CspAddMorphism to process names or
    -- channel names, if the name is not in the map in the morphism,
    -- then the application is the identity function. Thus empty maps
    -- are used to form the empty morphism.
    CspAddMorphism { channelMap = Map.empty
                   , processMap = Map.empty
                   }

-- | Pretty printing for Csp morphisms
instance Pretty CspAddMorphism where
  pretty = text . show

-- | Instance for CspCASL morphism extension (used for Category)
instance CASL_Morphism.MorphismExtension CspSign CspAddMorphism
    where
      ideMorphismExtension _ = emptyCspAddMorphism
      composeMorphismExtension = composeCspAddMorphism
      inverseMorphismExtension = inverseCspAddMorphism
      isInclusionMorphismExtension _ = True -- missing! BUG

-- Application of morhisms to sentences

-- | Apply a Signature Morphism to a CspCASL Sentence
mapSen :: CspMorphism -> CspCASLSen -> Result CspCASLSen
mapSen mor sen =
    if (CASL_Morphism.isInclusionMorphism
                     CASL_Morphism.isInclusionMorphismExtension) mor
    then return sen
    else case sen of
           CASLSen caslSen ->
               return $ CASLSen (mapCASLFormula mor caslSen)
           ProcessEq procName fqVarList commAlpha proc ->
               let -- Map the morphism over all the parts of the process
                   -- equation
                   newProcName = mapProcessName mor procName
                   newFqVarList = mapFQProcVarList mor fqVarList
                   newCommAlpha = mapCommAlpha mor commAlpha
                   newProc = mapProc mor proc
               in return (ProcessEq newProcName newFqVarList
                                    newCommAlpha newProc)

-- | Apply a signature morphism  to a Fully Qualified Process Variable List
mapFQProcVarList :: CspMorphism -> FQProcVarList -> FQProcVarList
mapFQProcVarList mor fqVarList =
    -- As these are terms, just map the morphism over CASL TERMs
    map (mapCASLTerm mor) fqVarList

-- | Apply a signature morphism  to a CommAlpha
mapCommAlpha :: CspMorphism -> CommAlpha -> CommAlpha
mapCommAlpha mor commAlpha = Set.map (mapCommType mor) commAlpha

-- | Apply a signature morphism to a CommType
mapCommType :: CspMorphism -> CommType -> CommType
mapCommType mor = mapCommTypeAux (sort_map mor) (channelMap $ extended_map mor)

-- | Apply a signature morphism to a process
mapProc :: CspMorphism -> PROCESS -> PROCESS
mapProc mor proc =
    let mapProc' = mapProc mor
        mapProcessName' = mapProcessName mor
        mapEvent' = mapEvent mor
        mapEventSet' = mapEventSet mor
        mapRenaming' = mapRenaming mor
        mapCommAlpha' = mapCommAlpha mor
        mapCASLTerm' = mapCASLTerm mor
        mapCASLFormula' = mapCASLFormula mor
    in case proc of
         --
         Skip r -> Skip r
         Stop r -> Stop r
         Div r -> Div r
         Run es r -> Run (mapEventSet' es) r
         Chaos ev r -> Chaos (mapEventSet' ev) r
         PrefixProcess e p r ->
             PrefixProcess (mapEvent' e) (mapProc' p) r
         Sequential p q r -> Sequential (mapProc' p) (mapProc' q) r
         ExternalChoice p q r -> ExternalChoice (mapProc' p) (mapProc' q) r
         InternalChoice p q r -> InternalChoice (mapProc' p) (mapProc' q) r
         Interleaving p q r -> Interleaving (mapProc' p) (mapProc' q) r
         SynchronousParallel p q r ->
             SynchronousParallel (mapProc' p) (mapProc' q) r
         GeneralisedParallel p es q r ->
             GeneralisedParallel (mapProc' p) (mapEventSet' es) (mapProc' q) r
         AlphabetisedParallel p les res q r ->
             AlphabetisedParallel (mapProc' p) (mapEventSet' les)
                                      (mapEventSet' res) (mapProc' q) r
         Hiding p es r ->
             Hiding (mapProc' p) (mapEventSet' es) r
         RenamingProcess p re r ->
             RenamingProcess (mapProc' p) (mapRenaming' re) r
         ConditionalProcess f p q r ->
             ConditionalProcess (mapCASLFormula' f)
                                    (mapProc' p) (mapProc' q) r
         NamedProcess pn fqParams  r ->
             NamedProcess (mapProcessName' pn) (map mapCASLTerm' fqParams) r
         FQProcess p commAlpha r ->
             FQProcess (mapProc' p) (mapCommAlpha' commAlpha) r

-- | Apply a signature morphism to an event set
mapEventSet :: CspMorphism -> EVENT_SET -> EVENT_SET
mapEventSet mor evs =
    case evs of
      EventSet _ _ ->
          -- There should be no EventSets (only FQEventSets) as the static
          -- analysis should have transformed EventSets into FQEventSets
          error "CspCASL.Morphism.mapEventSet: Unexpected EventSet"
      FQEventSet fqComms r -> FQEventSet (map (mapCommType mor) fqComms) r

-- | Apply a signature morphism to an event
mapEvent :: CspMorphism -> EVENT -> EVENT
mapEvent mor e =
    let mapEvent' = mapEvent mor
        mapCASLTerm' = mapCASLTerm mor
        mapSort' = CASL_MapSen.mapSrt mor
        mapChannelName' = mapChannelName mor
    in case e of
      TermEvent t r ->
          -- Just map the morphism over the event (a term)
          TermEvent (mapCASLTerm' t) r
      InternalPrefixChoice v s r ->
          -- Just map the morphism over the sort, we keep the variable name
          InternalPrefixChoice v (mapSort' s) r
      ExternalPrefixChoice v s r ->
          -- Just map the morphism over the sort, we keep the variable name
          ExternalPrefixChoice v (mapSort' s) r
      ChanSend c t r ->
          -- Just map the morphism over the event (a term) and the channel name
          ChanSend (mapChannelName' c) (mapCASLTerm' t) r
      ChanNonDetSend c v s r ->
          -- Just map the morphism over the sort and the channel name, we keep
          -- the variable name
          ChanNonDetSend (mapChannelName' c) v (mapSort' s) r
      ChanRecv c v s r ->
          -- Just map the morphism over the sort and the channel name, we keep
          -- the variable name
          ChanRecv (mapChannelName' c) v (mapSort' s) r
      FQEvent ev mfqc fqTerm r ->
          -- Map the morphism over each part of the FQEvent
          let mfqc' = case mfqc of
                        -- Just preserve nothings
                        Nothing -> Nothing
                        Just (chanName, chanSort) ->
                            -- Just map the morphism over the channel name and
                            -- channel sort
                            Just (mapChannelName' chanName, mapSort' chanSort)
          in FQEvent (mapEvent' ev) mfqc' (mapCASLTerm' fqTerm) r

mapRenaming :: CspMorphism -> RENAMING -> RENAMING
mapRenaming mor re =
    case re of
      Renaming _ ->
          -- There should be no (non fully qualified) Renamings (only
          -- FQRenamings) as the static analysis should have transformed
          -- EventSets into FQEventSets
          error "CspCASL.Morphism.mapRenaming: Unexpected Renaming"
      FQRenaming rs -> FQRenaming $ map (mapCASLTerm mor) rs

-- | Apply a signature morphism to a CASL TERM (for CspCASL only, i.e. a CASL
--   TERM that appears in CspCASL).
mapCASLTerm :: CspMorphism -> TERM () -> TERM ()
mapCASLTerm mor t =
    -- The error here is not used. It is a function to map over the morphism,
    -- CspCASL does not use this functionality.
    CASL_MapSen.mapTerm (error "CspCASL.Morphism.mapCASLTerm") mor t

-- | Apply a signature morphism to a CASL FORMULA (for CspCASL only, i.e. a CASL
--   FORMULA that appears in CspCASL).
mapCASLFormula :: CspMorphism -> FORMULA () -> FORMULA ()
mapCASLFormula mor f =
    -- The error here is not used. It is a function to map over the morphism,
    -- CspCASL does not use this functionality.
    CASL_MapSen.mapSen (error "CspCASL.Morphism.mapCASLFormula") mor f

-- | Apply a signature morphism to a channel name
mapChannelName :: CspMorphism -> CHANNEL_NAME -> CHANNEL_NAME
mapChannelName mor cn =
    let chanMap = channelMap $ CASL_Morphism.extended_map mor
    -- Find look up the new channel name, if it does not exist then
    -- use the original name.
    in Map.findWithDefault cn cn chanMap

-- | Apply a signature morphism to a process name
mapProcessName :: CspMorphism -> PROCESS_NAME -> PROCESS_NAME
mapProcessName mor pn =
    let procMap = processMap $ CASL_Morphism.extended_map mor
    -- Find look up the new process name, if it does not exist then
    -- use the original name.
    in Map.findWithDefault pn pn procMap

inducedCspSign :: Sort_map -> CspAddMorphism -> CspSign -> CspSign
inducedCspSign sm m sig = let
  cm = channelMap m
  newChans = Map.foldWithKey (\ c s ->
    Map.insert (Map.findWithDefault c c cm)
       (mapSort sm s)) Map.empty $ chans sig
  newProcs = Map.foldWithKey (\ p f ->
    Map.insert (Map.findWithDefault p p $ processMap m)
       (mapProcProfile sm cm f)) Map.empty $ procSet sig
  in sig { chans = newChans
         , procSet = newProcs }

mapProcProfile :: Sort_map -> Map.Map CHANNEL_NAME CHANNEL_NAME
               -> ProcProfile -> ProcProfile
mapProcProfile sm cm (ProcProfile sl cs) =
  ProcProfile (map (mapSort sm) sl) $ Set.map (mapCommTypeAux sm cm) cs

mapCommTypeAux :: Sort_map -> Map.Map CHANNEL_NAME CHANNEL_NAME
            -> CommType -> CommType
mapCommTypeAux sm cm ct = case ct of
   CommTypeSort s -> CommTypeSort $ mapSort sm s
   CommTypeChan (TypedChanName c s) ->
     CommTypeChan $ TypedChanName (Map.findWithDefault c c cm) $ mapSort sm s

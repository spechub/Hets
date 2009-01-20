{- |
Module      :  $Id$
Description :  Static analysis of CspCASL
Copyright   :  (c) Andy Gimblett, Liam O'Reilly Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Static analysis of CSP-CASL specifications, following "Tool Support
for CSP-CASL", MPhil thesis by Andy Gimblett, 2008.
<http://www.cs.swan.ac.uk/~csandy/mphil/>

-}

module CspCASL.StatAnaCSP where

import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as S
import CASL.AS_Basic_CASL (FORMULA(..), OpKind(..), SORT, TERM(..), VAR,
                           VAR_DECL(..))
import CASL.MixfixParser (emptyMix, Mix(..), makeRules, mkIdSets,
                          resolveFormula, resolveMixfix, unite)
import CASL.Overload (minExpFORMULA, oneExpTerm)
import CASL.Sign
import CASL.StaticAna (allOpIds, allPredIds)
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import qualified Common.Lib.Rel as Rel
import Common.Id (getRange, Id, nullRange, simpleIdToId)
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.LocalTop (Obligation(..), unmetObs)
import CspCASL.Print_CspCASL ()
import CspCASL.SignCSP
import CspCASL.Morphism(makeChannelNameSymbol, makeProcNameSymbol)

-- | The first element of the returned pair (CspBasicSpec) is the same
--   as the inputted version just with some very minor optimisations -
--   none in our case, but for CASL - brackets are otimized. This all
--   that happens, the mixfixed terms are still mixed fixed terms in
--   the returned version.
basicAnalysisCspCASL :: (CspBasicSpec, CspCASLSign, GlobalAnnos)
        -> Result (CspBasicSpec, ExtSign CspCASLSign Symbol,
                   [Named CspCASLSen])
basicAnalysisCspCASL (cc, sigma, ga) =
    let Result es mga = mergeGlobalAnnos ga $ globAnnos sigma
        (_, accSig) = runState (ana_BASIC_CSP cc) $ case mga of
              Nothing -> sigma
              Just nga -> sigma { globAnnos = nga }
        ds = reverse $ envDiags accSig
        -- Extract process equations only.
        ext = extendedInfo accSig
        ccsents = reverse $ ccSentences ext
        -- Clean signature here
        cleanSig = accSig
                   { extendedInfo = ext { ccSentences = []}}
    in Result (es ++ ds) $
      Just (cc, mkExtSign cleanSig, ccsents)

ana_BASIC_CSP :: CspBasicSpec -> State CspCASLSign ()
ana_BASIC_CSP cc = do checkLocalTops
                      mapM anaChanDecl (channels cc)
                      mapM anaProcItem (proc_items cc)
                      return ()

-- Analysis of local top elements

-- | Check a CspCASL signature for local top elements in its subsort
-- relation.
checkLocalTops :: State CspCASLSign ()
checkLocalTops = do
    sig <- get
    let obs = unmetObs $ Rel.toList $ Rel.transClosure $ sortRel sig
    addDiags (map lteError obs)
    return ()

-- | Add diagnostic error message for every unmet local top element
-- obligation.
lteError :: Obligation SORT -> Diagnosis
lteError (Obligation x y z) = mkDiag Error msg ()
    where msg = ("local top element obligation ("
                 ++ (show x) ++ "<" ++ (show y) ++ "," ++ (show z)
                 ++ ") unfulfilled")

-- Static analysis of channel declarations

-- | Statically analyse a CspCASL channel declaration.
anaChanDecl :: CHANNEL_DECL -> State CspCASLSign ()
anaChanDecl (ChannelDecl chanNames chanSort) = do
    checkSorts [chanSort] -- check channel sort is known
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
    newChanMap <- Monad.foldM (anaChannelName chanSort) oldChanMap chanNames
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }
            , envDiags = vds
            }
    return ()

-- | Statically analyse a CspCASL channel name.
anaChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME ->
                    State CspCASLSign ChanNameMap
anaChannelName s m chanName = do
    sig <- get
    if (show chanName) `S.member` (S.map show (sortSet sig))
      then do let err = "channel name already in use as a sort name"
              addDiags [mkDiag Error err chanName]
              return m
      else case Map.lookup chanName m of
             Nothing ->
                 -- Add the channel name as a symbol to the list of
                 -- newly defined symbols - which is stored in the CASL
                 -- signature
                 do addSymbol (makeChannelNameSymbol chanName)
                    return (Map.insert chanName s m) -- insert new.
             Just e ->
               if e == s
                 then do let warn = "channel redeclared with same sort"
                         addDiags [mkDiag Warning warn chanName]
                         return m -- already declared with this sort.
                 else do let err = "channel declared with multiple sorts"
                         addDiags [mkDiag Error err chanName]
                         return m

-- Static analysis of process items

-- | Statically analyse a CspCASL process item.
anaProcItem :: PROC_ITEM -> State CspCASLSign ()
anaProcItem procItem =
    case procItem of
      (Proc_Decl name argSorts alpha) -> anaProcDecl name argSorts alpha
      (Proc_Eq parmProcName procTerm) -> anaProcEq parmProcName procTerm

-- Static analysis of process declarations

-- | Statically analyse a CspCASL process declaration.
anaProcDecl :: PROCESS_NAME -> PROC_ARGS -> PROC_ALPHABET
            -> State CspCASLSign ()
anaProcDecl name argSorts (ProcAlphabet commTypes _) = do
    sig <- get
    let ext = extendedInfo sig
        oldProcDecls = procSet ext
    newProcDecls <-
      if name `Map.member` oldProcDecls
        then do -- duplicate process declaration
                let err = "process name declared more than once"
                addDiags [mkDiag Error err name]
                return oldProcDecls
        else do -- new process declation
                checkSorts argSorts -- check argument sorts are known
                -- build alphabet: set of CommType values. We do not
                -- need the fully qualfied commTypes that are returned
                -- (these area used for analysing Event Sets)
                (alpha, _ ) <- Monad.foldM (anaCommType sig) (S.empty, []) commTypes
                let profile = (ProcProfile argSorts alpha)
                -- Add the process name as a symbol to the list of
                -- newly defined symbols - which is stored in the CASL
                -- signature
                addSymbol (makeProcNameSymbol name)
                return (Map.insert name profile oldProcDecls)
    vds <- gets envDiags
    put sig { extendedInfo = ext {procSet = newProcDecls }
            , envDiags = vds
            }
    return ()

-- Static analysis of process equations

-- | Statically analyse a CspCASL process equation.
anaProcEq :: PARM_PROCNAME -> PROCESS -> State CspCASLSign ()
anaProcEq (ParmProcname pn vs) proc = do
    sig <- get
    let ext = extendedInfo sig
        ccsens = ccSentences ext
        procDecls = procSet ext
        prof = pn `Map.lookup` procDecls
    case prof of
         -- Only analyse a process if its name (and thus profile) is known
         Just (ProcProfile procArgs procAlpha) ->
             do  gVars <- anaProcVars pn procArgs vs -- compute global
                 -- vars Change a procVarList to a FQProcVarList We do
                 -- not care about the range as we are building fully
                 -- qualified variables and they have already been
                 -- checked to be ok.
                 let mkFQProcVar (v,s) = Qual_var v s nullRange
                 let fqGVars = map mkFQProcVar gVars
                 (termAlpha, fqProc) <- anaProcTerm proc (Map.fromList gVars) Map.empty
                 checkCommAlphaSub termAlpha procAlpha proc "process equation"
                 -- Save the diags from the checkCommAlphaSub
                 vds <- gets envDiags
                 -- put CspCASL Sentences back in to the state with new sentence
                 put sig {envDiags = vds, extendedInfo =
                          ext { ccSentences =
                                -- BUG - What should the constituent
                                -- alphabet be for this process?
                                -- probably the same as the inner one!
                                (makeNamed ("ProcHugo")
                                               (ProcessEq pn fqGVars
                                                          S.empty
                                                          fqProc)):ccsens
                              }
                         }
                 return ()
         Nothing ->
             do addDiags [mkDiag Error
                          "process equation for unknown process" pn]
                return ()
    return ()

-- | Statically analyse a CspCASL process equation's global variable
-- names.
anaProcVars :: PROCESS_NAME -> [SORT] -> [VAR] -> State CspCASLSign ProcVarList
anaProcVars pn ss vs =
    do vars <-
           case (compare (length ss) (length vs)) of
             LT -> do addDiags [mkDiag Error "too many process arguments" pn]
                      return []
             GT -> do addDiags [mkDiag Error "not enough process arguments" pn]
                      return []
             EQ -> Monad.foldM anaProcVar [] (zip vs ss)
       return $ reverse $ vars

-- | Statically analyse a CspCASL process-global variable name.
anaProcVar :: ProcVarList -> (VAR, SORT) -> State CspCASLSign ProcVarList
anaProcVar old (v, s) = do
    if v `elem` (map fst old)
       then do addDiags [mkDiag Error
                         "process argument declared more than once" v]
               return old
       else return ((v,s) : old)

-- Static analysis of process terms

-- BUG in fucntion below
-- not returing FQProcesses
-- | Statically analyse a CspCASL process term.
--   The process that is returned is a fully qualified process.
anaProcTerm :: PROCESS -> ProcVarMap -> ProcVarMap ->
               State CspCASLSign (CommAlpha, PROCESS)
anaProcTerm proc gVars lVars = case proc of
    NamedProcess name args range ->
        do addDiags [mkDiag Debug "Named process" proc]
           (al, fqArgs) <- anaNamedProc proc name args (lVars `Map.union` gVars)
           let fqProc = FQProcess (NamedProcess name fqArgs range) al range
           return (al, fqProc)
    Skip range ->
        do addDiags [mkDiag Debug "Skip" proc]
           let fqProc = FQProcess (Skip range) S.empty range
           return (S.empty, fqProc)
    Stop range ->
        do addDiags [mkDiag Debug "Stop" proc]
           let fqProc = FQProcess (Stop range) S.empty range
           return (S.empty, fqProc)
    Div range ->
        do addDiags [mkDiag Debug "Div" proc]
           let fqProc = FQProcess (Div range) S.empty range
           return (S.empty, fqProc)
    Run es range ->
        do addDiags [mkDiag Debug "Run" proc]
           (comms, fqEs) <- anaEventSet es
           let fqProc = FQProcess (Run fqEs range) comms range
           return (comms, fqProc)
    Chaos es range ->
        do addDiags [mkDiag Debug "Chaos" proc]
           (comms, fqEs) <- anaEventSet es
           let fqProc = FQProcess (Chaos fqEs range) comms range
           return (comms, fqProc)
    PrefixProcess e p range ->
        do addDiags [mkDiag Debug "Prefix" proc]
           (evComms, rcvMap, fqEvent) <- anaEvent e (lVars `Map.union` gVars)
           (comms, pFQTerm) <- anaProcTerm p gVars (rcvMap `Map.union` lVars)
           let newAlpha = comms `S.union` evComms
           let fqProc = FQProcess (PrefixProcess fqEvent pFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    InternalPrefixProcess v s p range ->
        -- BUG - Not returning a complete fully qualified process
        do addDiags [mkDiag Debug "Internal prefix" proc]
           checkSorts [s] -- check sort is known
           (comms, pFQTerm) <- anaProcTerm p gVars (Map.insert v s lVars)
           let newAlpha = S.insert (CommTypeSort s) comms
           let fqProc = FQProcess (InternalPrefixProcess v s pFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    ExternalPrefixProcess v s p range ->
        -- BUG - Not returning a complete fully qualified process
        do addDiags [mkDiag Debug "External prefix" proc]
           checkSorts [s] -- check sort is known
           (comms, pFQTerm) <- anaProcTerm p gVars (Map.insert v s lVars)
           let newAlpha = S.insert (CommTypeSort s) comms
           let fqProc = FQProcess (ExternalPrefixProcess v s pFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    Sequential p q range ->
        do addDiags [mkDiag Debug "Sequential" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars Map.empty
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (Sequential pFQTerm qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    InternalChoice p q range ->
        do addDiags [mkDiag Debug "InternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (InternalChoice pFQTerm qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    ExternalChoice p q range ->
        do addDiags [mkDiag Debug "ExternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (ExternalChoice pFQTerm qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    Interleaving p q range ->
        do addDiags [mkDiag Debug "Interleaving" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (Interleaving pFQTerm qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    SynchronousParallel p q range ->
        do addDiags [mkDiag Debug "Synchronous" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (SynchronousParallel pFQTerm qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    GeneralisedParallel p es q range ->
        do addDiags [mkDiag Debug "Generalised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (synComms, fqEs) <- anaEventSet es
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = S.unions [pComms, qComms, synComms]
           let fqProc = FQProcess (GeneralisedParallel pFQTerm fqEs qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    AlphabetisedParallel p esp esq q range ->
        do addDiags [mkDiag Debug "Alphabetised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (pSynComms, fqEsp) <- anaEventSet esp
           checkCommAlphaSub pSynComms pComms proc
                                 "alphabetised parallel, left"
           (qSynComms, fqEsq) <- anaEventSet esq
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           checkCommAlphaSub qSynComms qComms proc
                                 "alphabetised parallel, right"
           let newAlpha = pComms `S.union` qComms
           let fqProc = FQProcess (AlphabetisedParallel pFQTerm fqEsp fqEsq qFQTerm range) newAlpha range
           return (newAlpha, fqProc)
    Hiding p es range ->
        do addDiags [mkDiag Debug "Hiding" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (hidComms, fqEs) <- anaEventSet es
           return (pComms `S.union` hidComms,
                   FQProcess (Hiding pFQTerm fqEs range) (pComms `S.union` hidComms) range)
    RenamingProcess p renaming range ->
        do addDiags [mkDiag Debug "Renaming" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (renAlpha, fqRenaming) <- anaRenaming renaming
           let newAlpha = pComms `S.union` renAlpha
           let fqProc = FQProcess (RenamingProcess pFQTerm fqRenaming range) (pComms `S.union` renAlpha) range
           return (newAlpha, fqProc)
    ConditionalProcess f p q range ->
        do addDiags [mkDiag Debug "Conditional" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           -- mfs is the fully qualified formula version of f
           mfs <- anaFormulaCspCASL (gVars `Map.union` lVars) f
           let fFQ = case mfs of
                       Nothing -> f -- use old formula as the fully
                                    -- qualified version - there is a
                                    -- error in the spec anyway as the
                                    -- formula could not be fully
                                    -- qualified.
                       Just fs -> fs -- use the real fully qualified formula
           let fComms = case mfs of
                          Nothing -> S.empty
                          Just fs -> formulaComms fs
           let newAlpha = S.unions [pComms, qComms, fComms]
           let fqProc = FQProcess (ConditionalProcess
                                   (fFQ) pFQTerm qFQTerm range)
                        newAlpha range
           return (newAlpha, fqProc)
    FQProcess _ _ _ -> error "CspCASL.StatAnaCSP.anaProcTerm: Unexpected FQProcess"

-- | Statically analyse a CspCASL "named process" term. Return the
--   permitted alphabet of the process and also a list of the fully qualified
--   version of the inputted terms.
anaNamedProc :: PROCESS -> PROCESS_NAME -> [TERM ()] -> ProcVarMap ->
                State CspCASLSign (CommAlpha, [TERM ()])
anaNamedProc proc pn terms procVars = do
    sig <- get
    let ext = extendedInfo sig
        procDecls = procSet ext
        prof = pn `Map.lookup` procDecls
    case prof of
      Just (ProcProfile varSorts permAlpha) ->
        if (length terms) == (length varSorts)
          then do fqTerms <- mapM (anaNamedProcTerm procVars) (zip terms varSorts)
                  -- Return the permitted alphabet of the process and
                  -- the fully qualifed terms
                  return (permAlpha, fqTerms)
          else do let err = "wrong number of arguments in named process"
                  addDiags [mkDiag Error err proc]
                  -- Return the empty alphabet and the original
                  -- terms. There is an error in the spec.
                  return (S.empty, terms)
      Nothing ->
        do addDiags [mkDiag Error "unknown process name" proc]
           -- Return the empty alphabet and the original
           -- terms. There is an error in the spec.
           return (S.empty, terms)

-- | Statically analysis a CASL term occurring in a CspCASL "named
-- process" term.
anaNamedProcTerm :: ProcVarMap -> ((TERM ()), SORT) -> State CspCASLSign (TERM ())
anaNamedProcTerm pm (t, expSort) = do
    mt <- anaTermCspCASL pm t
    case mt of
      Nothing -> return t -- CASL term analysis failed. Use old term
                          -- as the fully qualified term, there is a
                          -- error in the spec anyway.
      (Just at) -> do at' <- ccTermCast at expSort -- attempt cast;
                      case at' of
                        Nothing -> -- Use old term as the fully
                                   -- qualified term, there is a error
                                   -- in the spec anyway.
                               return t
                        (Just at'') -> return at'' -- Use the fully
                                                   -- qualified
                                                   -- (possibly cast)
                                                   -- term

-- Static analysis of event sets and communication types

-- | Statically analyse a CspCASL event set. Returns the alphabet of
--   the event set and a fully qualified version of the event set.
anaEventSet :: EVENT_SET -> State CspCASLSign (CommAlpha, EVENT_SET)
anaEventSet eventSet =
    case eventSet of
      EventSet es r ->
          do sig <- get
             -- fqEsElems is built the reversed order for efficiency.
             (comms, fqEsElems) <- Monad.foldM (anaCommType sig)
                                   (S.empty, []) es
             vds <- gets envDiags
             put sig { envDiags = vds }
             -- reverse the list inside the event set
             return (comms, FQEventSet (reverse fqEsElems) r)
      FQEventSet _ _ ->
          error "CspCASL.StatAnaCSP.anaEventSet: Unexpected FQEventSet"

-- | Statically analyse a CspCASL communication type. Returns the
--   extended alphabet and the extended list of fully qualified event
--   set elements - [CommType].
anaCommType :: CspCASLSign -> (CommAlpha, [CommType]) -> COMM_TYPE ->
               State CspCASLSign (CommAlpha, [CommType])
anaCommType sig (alpha, fqEsElems) ct =
    if ctSort `S.member` (sortSet sig)
      then -- ct is a sort name; insert sort into alpha and add a sort
           -- to the fully qualified event set elements.
        do let newAlpha = S.insert (CommTypeSort ctSort) alpha
           let newFqEsElems = (CommTypeSort ctSort) : fqEsElems
           return (newAlpha, newFqEsElems)
      else -- ct not a sort name, so should be a channel name
        case Map.lookup ct (chans $ extendedInfo sig) of
          Just s -> -- ct is a channel name; insert typed chan name
                    -- into alpha and add typed channel to the fully
                    -- qualified event set elemenets.
                    let newAlpha = S.insert (mkTypedChan ct s) alpha
                        newFqEsElems = (mkTypedChan ct s) : fqEsElems
                    in return (newAlpha, newFqEsElems)
          Nothing -> do let err = "not a sort or channel name"
                        addDiags [mkDiag Error err ct]
                        -- failed, thus error in spec, return the
                        -- unmodified alphabet and the unmodifled
                        -- fully qualified event set elements.
                        return (alpha, fqEsElems)
        where ctSort = simpleIdToId ct
              mkTypedChan c s = CommTypeChan $ TypedChanName c s

-- Static analysis of events

-- | Statically analyse a CspCASL event. Returns a constituent
--   communication alphabet of the event, mapping for any new
--   locally bound variables and a fully qualified version of the event.
anaEvent :: EVENT -> ProcVarMap -> State CspCASLSign (CommAlpha, ProcVarMap, EVENT)
anaEvent e vars =
    case e of
      TermEvent t r ->
          do (alpha, newVars, fqTerm) <- anaTermEvent t vars
             let fqEvent = FQEvent e Nothing fqTerm r
             return (alpha, newVars, fqEvent)
      ChanSend c t r ->
          do -- mfqChan is a maybe fully qualified
             -- channel. It will ne Nothing if
             -- annChanSend failed - i.e. we forget
             -- about the channel.
            (alpha, newVars, mfqChan, fqTerm) <- anaChanSend c t vars
            let fqEvent = FQEvent e mfqChan fqTerm r
            return (alpha, newVars, fqEvent)
      ChanNonDetSend c v s r ->
          -- mfqChan is the same as in chanSend case.
          -- fqVar is the fully qualfied version of the variable.
          do (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQEvent e mfqChan fqVar r
             return (alpha, newVars, fqEvent)
      ChanRecv c v s r ->
          -- mfqChan is the same as in chanSend case.
          -- fqVar is the fully qualfied version of the variable.
          do (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQEvent e mfqChan fqVar r
             return (alpha, newVars, fqEvent)
      FQEvent _ _ _ _ ->
          error "CspCASL.StatAnaCSP.anaEvent: Unexpected FQEvent"

-- | Statically analyse a CspCASL term event. Returns a constituent
--   communication alphabet of the event and a mapping for any new
--   locally bound variables and the fully qualified version of the
--   term.
anaTermEvent :: (TERM ()) -> ProcVarMap ->
                State CspCASLSign (CommAlpha, ProcVarMap, TERM ())
anaTermEvent t vars = do
  mt <- anaTermCspCASL vars t
  let (alpha, t') = case mt of
                      -- return the alphabet and the fully qualified term
                      Just at -> ([(CommTypeSort (sortOfTerm at))], at)
                      -- return the empty alphabet and the original term
                      Nothing -> ([], t)
  return (S.fromList alpha, Map.empty, t')

-- | Statically analyse a CspCASL channel send event. Returns a
--   constituent communication alphabet of the event, a mapping for
--   any new locally bound variables, a fully qualified channel (if
--   possible) and the fully qualified version of the term.
anaChanSend :: CHANNEL_NAME -> (TERM ()) -> ProcVarMap ->
                State CspCASLSign (CommAlpha, ProcVarMap,
                                   (Maybe (CHANNEL_NAME, SORT)), TERM ())
anaChanSend c t vars = do
  sig <- get
  let ext = extendedInfo sig
  case c `Map.lookup` (chans ext) of
    Nothing -> do
      addDiags [mkDiag Error "unknown channel" c]
      -- Use old term as the fully qualified term and forget about the
      -- channel, there is an error in the spec
      return (S.empty, Map.empty, Nothing, t)
    Just chanSort -> do
      mt <- anaTermCspCASL vars t
      case mt of
        Nothing -> -- CASL analysis failed. Use old term as the fully
                   -- qualified term and forget about the channel,
                   -- there is an error in the spec.
                   return (S.empty, Map.empty, Nothing, t)
        (Just at) ->
            do mc <- ccTermCast at chanSort
               case mc of
                 Nothing -> -- cast failed. Use old term as the fully
                            -- qualified term, and forget about the
                            -- channel there is an error in the spec.
                            return (S.empty, Map.empty, Nothing, t)
                 (Just ct) ->
                     do let castSort = sortOfTerm ct
                            alpha = [CommTypeSort castSort
                                    ,CommTypeChan $ TypedChanName c castSort
                                    ]
                        -- Use the real fully qualified term. We do
                        -- not want to use a cast term here. A cast
                        -- must be possible, but we do not want to
                        -- force it!
                        return (S.fromList alpha, Map.empty,
                                 Just (c, chanSort), at)

-- | Statically analyse a CspCASL "binding" channel event (which is
-- either a channel nondeterministic send event or a channel receive
-- event). Returns a constituent communication alphabet of the event,
-- a mapping for any new locally bound variables, a fully qualified
-- channel (if possible) and the fully qualified version of the
-- variable.
anaChanBinding :: CHANNEL_NAME -> VAR -> SORT ->
                   State CspCASLSign (CommAlpha, ProcVarMap, (Maybe (CHANNEL_NAME, SORT)), TERM ())
anaChanBinding c v s = do
  checkSorts [s] -- check sort is known
  sig <- get
  let ext = extendedInfo sig
  case c `Map.lookup` (chans ext) of
    Nothing -> do
      addDiags [mkDiag Error "unknown channel" c]
      -- No fully qualified channel, use Nothing - there is a error in
      -- the spec anyway. Use the real fully qualified variable
      -- version with a nullRange.
      return (S.empty, Map.empty, Nothing, (Qual_var v s nullRange))
    Just chanSort -> do
      if s `S.member` (chanSort `S.insert` (subsorts chanSort))
        then do let alpha = [CommTypeSort s
                            ,CommTypeChan (TypedChanName c s)]
                let binding = [(v, s)]
                              -- Return the alphabet, var mapping, the
                              -- fully qualfied channel and fully
                              -- qualfied variable
                return (S.fromList alpha, Map.fromList binding,
                             (Just (c,chanSort)), (Qual_var v s nullRange))
        else do let err = "sort not a subsort of channel's sort"
                addDiags [mkDiag Error err s]
                         -- There is a error in the spec, but return
                         -- the alphabet, var mapping, the fully
                         -- qualfied channel and fully qualfied
                         -- variable - as we can.
                return (S.empty, Map.empty, (Just (c,chanSort)),
                             (Qual_var v s nullRange))
                    where subsorts = Rel.predecessors (sortRel sig)

-- Static analysis of renaming and renaming items

-- | Statically analyse a CspCASL renaming. Returns the alphabet and
-- | the fully qualified renaming.
anaRenaming :: RENAMING -> State CspCASLSign (CommAlpha, RENAMING)
anaRenaming renaming = case renaming of
  Renaming r -> do
    (al, fqRenamingTermsMaybes) <- Monad.foldM anaRenamingItem (S.empty, []) r
    return (al, FQRenaming fqRenamingTermsMaybes)
  FQRenaming _ ->
      error "CspCASL.StatAnaCSP.anaRenaming: Unexpected FQRenaming"

-- | Statically analyse a CspCASL renaming item. Return the alphabet
-- | and the fully qualified list of renaming functions and predicates.
anaRenamingItem :: (CommAlpha, [TERM ()]) -> Id ->
                   State CspCASLSign (CommAlpha, [TERM ()])
anaRenamingItem (inAl, fqRenamingTerms) ri = do
-- BUG -- too many nothings - should only be one
  totOps <- getUnaryOpsById ri Total
  if (not $ S.null totOps)
    then return (inAl `S.union` totOps, fqRenamingTerms)
    else do
      parOps <- getUnaryOpsById ri Partial
      if not (S.null parOps)
        then return (inAl `S.union` parOps, fqRenamingTerms)
        else do
          preds <- getBinPredsById ri
          if not (S.null preds)
            then return (inAl `S.union` preds, fqRenamingTerms)
            else do
              let err = "renaming item not a binary "
                        ++ "operation or predicate name"
              addDiags [mkDiag Error err ri]
              -- return the original alphabet and the original fully
              -- qualified terms (renamings) with out any modification
              -- as there is an error in the spec.
              return (inAl, fqRenamingTerms)

-- | Given a CASL identifier and a `function kind' (total or partial),
-- find all unary operations of that kind with that name in the CASL
-- signature, and return a set of corresponding communication types
-- for those operations.
getUnaryOpsById :: Id -> OpKind -> State CspCASLSign (S.Set CommType)
getUnaryOpsById ri kind = do
    sig <- get
    let opsWithId = Map.findWithDefault S.empty ri (opMap sig)
        binOpsKind = S.filter (isBin kind) opsWithId
        cts = S.map CommTypeSort $ S.fold opSorts S.empty binOpsKind
    return cts
      where isBin k ot = (k == opKind ot) && (1 == (length (opArgs ot)))
            opSorts o inS = inS `S.union` (S.fromList ((opArgs o) ++ [opRes o]))

-- | Given a CASL identifier find all binary predicates with that name
-- in the CASL signature, and return a set of corresponding
-- communication types for those predicates.
getBinPredsById :: Id -> State CspCASLSign (S.Set CommType)
getBinPredsById ri = do
    sig <- get
    let predsWithId = Map.findWithDefault S.empty ri (predMap sig)
        binPreds = S.filter isBin predsWithId
        cts = S.map CommTypeSort $ S.fold predSorts S.empty binPreds
    return cts
      where isBin ot = (2 == (length (predArgs ot)))
            predSorts p inS = inS `S.union` (S.fromList (predArgs p))

-- | Given two CspCASL communication alphabets, check that the first's
-- subsort closure is a subset of the second's subsort closure.
checkCommAlphaSub :: CommAlpha -> CommAlpha -> PROCESS -> String ->
                     State CspCASLSign ()
checkCommAlphaSub sub super proc context = do
  sig <- get
  let extras = ((closeCspCommAlpha sig sub) `S.difference`
                (closeCspCommAlpha sig super))
  if S.null extras
    then do return ()
    else do let err = ("Communication alphabet subset violations (" ++
                       context ++ "): " ++ (show $ S.toList extras))
            addDiags [mkDiag Error err proc]
            return ()

-- Static analysis of CASL terms occurring in CspCASL process terms.

-- | Statically analyse a CASL term appearing in a CspCASL process;
-- any in-scope process variables are added to the signature before
-- performing the analysis.
anaTermCspCASL :: ProcVarMap -> (TERM ()) ->
                  State CspCASLSign (Maybe (TERM ()))
anaTermCspCASL pm t = do
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaTermCspCASL' sigext t
    addDiags ds
    return mt

-- | Statically analyse a CASL term in the context of a CspCASL
-- signature.  If successful, returns a fully-qualified term.
anaTermCspCASL' :: CspCASLSign -> TERM () -> Result (TERM ())
anaTermCspCASL' sig trm = do
    let allIds = unite [mkIdSets (allOpIds sig) $ allPredIds sig]
        ga = globAnnos sig
        mix = emptyMix { mixRules = makeRules ga allIds }
    resT <- resolveMixfix (putParen mix) (mixResolve mix)
                 ga (mixRules mix) trm
    oneExpTerm (const return) sig resT

-- | Attempt to cast a CASL term to a particular CASL sort.
ccTermCast :: (TERM ()) -> SORT -> State CspCASLSign (Maybe (TERM ()))
ccTermCast t cSort =
    if termSort == (cSort)
      then return (Just t)
      else do sig <- get
              if Rel.member termSort cSort (sortRel sig)
                then do let err = "upcast term to " ++ (show cSort)
                        addDiags [mkDiag Debug err t]
                        return (Just (Sorted_term t cSort (getRange t)))
                else if Rel.member cSort termSort (sortRel sig)
                       then do let err = "downcast term to " ++ (show cSort)
                               addDiags [mkDiag Debug err t]
                               return (Just (Cast t cSort (getRange t)))
                       else do let err = "can't cast term to sort " ++
                                           (show cSort)
                               addDiags [mkDiag Error err t]
                               return Nothing
        where termSort = (sortOfTerm t)

-- Static analysis of CASL formulae occurring in CspCASL process
-- terms.

-- | Statically analyse a CASL formula appearing in a CspCASL process;
-- any in-scope process variables are added to the signature before
-- performing the analysis.
anaFormulaCspCASL :: ProcVarMap -> (FORMULA ()) ->
                     State CspCASLSign (Maybe (FORMULA ()))
anaFormulaCspCASL pm f = do
    addDiags [mkDiag Debug "anaFormulaCspCASL" f]
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaFormulaCspCASL' sigext f
    addDiags ds
    return mt

-- | Statically analyse a CASL formula in the context of a CspCASL
-- signature.  If successful, returns a fully-qualified formula.
anaFormulaCspCASL' :: CspCASLSign -> FORMULA () -> Result (FORMULA ())
anaFormulaCspCASL' sig frm = do
    let allIds = unite [mkIdSets (allOpIds sig) $ allPredIds sig]
        ga = globAnnos sig
        mix = emptyMix { mixRules = makeRules ga allIds }
    resF <- resolveFormula (putParen mix) (mixResolve mix) ga (mixRules mix) frm
    minExpFORMULA (const return) sig resF

-- | Compute the communication alphabet arising from a formula
-- occurring in a CspCASL process term.
formulaComms :: (FORMULA ()) -> CommAlpha
formulaComms f = case f of
    Quantification _ varDecls f' _ ->
        (formulaComms f') `S.union` S.fromList vdSorts
            where vdSorts = (map (CommTypeSort . vdSort) varDecls)
                  vdSort (Var_decl _ s _) = s
    Conjunction fs _ -> S.unions (map formulaComms fs)
    Disjunction fs _ -> S.unions (map formulaComms fs)
    Implication f1 f2 _ _ -> (formulaComms f1) `S.union` (formulaComms f2)
    Equivalence f1 f2 _ -> (formulaComms f1) `S.union` (formulaComms f2)
    Negation f' _ -> formulaComms f'
    True_atom _ -> S.empty
    False_atom _ -> S.empty
    Predication _ _ _ -> S.empty
    Definedness t _ -> S.singleton (CommTypeSort (sortOfTerm t))
    Existl_equation t1 t2 _ -> S.fromList [CommTypeSort (sortOfTerm t1),
                                           CommTypeSort (sortOfTerm t2)]
    Strong_equation t1 t2 _ -> S.fromList [CommTypeSort (sortOfTerm t1),
                                           CommTypeSort (sortOfTerm t2)]
    Membership t s _ -> S.fromList [CommTypeSort (sortOfTerm t),
                                    CommTypeSort s]
    Mixfix_formula t -> S.singleton (CommTypeSort (sortOfTerm t))
    Unparsed_formula _ _ -> S.empty
    Sort_gen_ax _ _ -> S.empty
    ExtFORMULA _ -> S.empty

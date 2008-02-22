{- |
Module      :  $Id$
Description :  static analysis for CspCASL
Copyright   :  (c) Markus Roggenbach, Till Mossakowski, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Static analysis for CSP-CASL

-}

module CspCASL.StatAnaCSP where

import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

import CASL.AS_Basic_CASL (SORT, TERM, VAR)
import CASL.Sign
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import qualified Common.Lib.Rel as Rel
import Common.Id (simpleIdToId)
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.LocalTop (Obligation(..), unmetObs)
import CspCASL.Print_CspCASL ()
import CspCASL.SignCSP

basicAnalysisCspCASL :: (CspBasicSpec, CspSign, GlobalAnnos)
        -> Result (CspBasicSpec, ExtSign CspSign (), [Named ()])
basicAnalysisCspCASL (cc, sigma, _ga) = do
    let (_, accSig) = runState (ana_BASIC_CSP cc) sigma
    let ds = reverse $ envDiags accSig
    Result ds (Just ()) -- insert diagnostics
    return (cc, mkExtSign accSig, [])

ana_BASIC_CSP :: CspBasicSpec -> State CspSign ()
ana_BASIC_CSP cc = do checkLocalTops
                      mapM anaChanDecl (channels cc)
                      mapM anaProcItem (proc_items cc)
                      return ()

-- Analysis of local top elements

-- | Check CspCASL signature for local top elements in subsorts.
checkLocalTops :: State CspSign ()
checkLocalTops = do
    sig <- get
    let obs = unmetObs $ Rel.toList $ Rel.transClosure $ sortRel sig
    addDiags (map lteError obs)
    return ()

-- | Add diagnostic error for every unmet local top element obligation.
lteError :: Obligation SORT -> Diagnosis
lteError (Obligation x y z) = mkDiag Error msg ()
    where msg = ("local top element obligation ("
                 ++ (show x) ++ "<" ++ (show y) ++ "," ++ (show z)
                 ++ ") unfulfilled")

-- Analysis of channel declarations

anaChanDecl :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChanDecl (ChannelDecl chanNames chanSort) = do
    checkSorts [chanSort]
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
    newChanMap <- Monad.foldM (anaChannelName chanSort) oldChanMap chanNames
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }
            , envDiags = vds
            }
    return (ChannelDecl chanNames chanSort)

anaChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME ->
                    State CspSign ChanNameMap
anaChannelName s m chanName = do
    sig <- get
    if Set.member (show chanName) (Set.map show (sortSet sig))
      then do let err = "channel name already in use as a sort name"
              addDiags [mkDiag Error err chanName]
              return m
      else case Map.lookup chanName m of
             Nothing -> return (Map.insert chanName s m) -- insert new.
             Just e ->
               if e == s
                 then do let warn = "channel redeclared with same sort"
                         addDiags [mkDiag Warning warn chanName]
                         return m -- already declared with this sort.
                 else do let err = "channel declared with multiple sorts"
                         addDiags [mkDiag Error err chanName]
                         return m

-- Analysis of process items

anaProcItem :: PROC_ITEM -> State CspSign ()
anaProcItem procItem =
    case procItem of
      (Proc_Decl name argSorts alpha) -> anaProcDecl name argSorts alpha
      (Proc_Eq parmProcName procTerm) -> anaProcEq parmProcName procTerm

-- Analysis of process declarations

anaProcDecl :: PROCESS_NAME -> PROC_ARGS -> PROC_ALPHABET
            -> State CspSign ()
anaProcDecl name argSorts (ProcAlphabet cts _) = do
    sig <- get
    let ext = extendedInfo sig
        oldProcDecls = procSet ext
    newProcDecls <- -- add new declaration to modify
        if name `Map.member` oldProcDecls
        then do -- duplicate process declaration
                let err = "process name declared more than once"
                addDiags [mkDiag Error err name]
                return oldProcDecls
        else do -- new process declation
                checkSorts argSorts
                alpha <- Monad.foldM (checkCommType sig) Set.empty cts
                let profile = (ProcProfile argSorts alpha)
                return (Map.insert name profile oldProcDecls)
    vds <- gets envDiags
    put sig { extendedInfo = ext {procSet = newProcDecls }
            , envDiags = vds
            }
    return ()

checkCommType :: CspSign -> CommAlpha -> COMM_TYPE -> State CspSign CommAlpha
checkCommType sig alpha ct =
    if Set.member ctSort $ sortSet sig
    then do return (Set.insert (CommTypeSort ctSort) alpha)
    else case Map.lookup ct (chans $ extendedInfo sig) of
           Just s -> return (Set.insert (CommTypeChan (TypedChanName ct s)) alpha)
           Nothing -> do let err = "not a sort or channel name"
                         addDiags [mkDiag Error err ct]
                         return alpha
        where ctSort = simpleIdToId ct

-- Analysis of process equations

anaProcEq :: PARM_PROCNAME -> PROCESS -> State CspSign ()
anaProcEq (ParmProcname pn vs) proc = do
    sig <- get
    let ext = extendedInfo sig
        procDecls = procSet ext
        prof = pn `Map.lookup` procDecls
    case prof of
      -- Only analyse a process if its name (and thus profile) is known
      Just pf -> do gVars <- anaProcVars pn (procArgs pf) vs
                    anaProcess proc (procAlphabet pf) gVars Map.empty
                    return ()
      Nothing -> do addDiags [mkDiag Error "unknown process" pn]
                    return ()
    vds <- gets envDiags
    put sig { envDiags = vds }
    return ()




anaProcVars :: PROCESS_NAME -> [SORT] -> [VAR] -> State CspSign ProcVarMap
anaProcVars pn ss vs = do
    case (compare (length ss) (length vs)) of
       LT -> do addDiags [mkDiag Error "too many process arguments" pn]
                return Map.empty
       GT -> do addDiags [mkDiag Error "not enough process arguments" pn]
                return Map.empty
       EQ -> do vm <- Monad.foldM anaProcVar Map.empty (zip vs ss)
                return vm

anaProcVar :: ProcVarMap -> (VAR, SORT) -> State CspSign ProcVarMap
anaProcVar old (v, s) = do
    if v `Map.member` old
       then do addDiags [mkDiag Error "process arg declared more than once" v]
               return old
       else return (Map.insert v s old)

-- Analysis of process terms

anaProcess :: PROCESS -> CommAlpha -> ProcVarMap ->
              ProcVarMap -> State CspSign CommAlpha
anaProcess proc alpha gVars lVars = do
    case proc of
      Skip _ ->
          do addDiags [mkDiag Debug "Skip" proc]
             return Set.empty
      Stop _ ->
          do addDiags [mkDiag Debug "Stop" proc]
             return Set.empty
      Div _ ->
          do addDiags [mkDiag Debug "Div" proc]
             return Set.empty
      Run es _ ->
          do addDiags [mkDiag Debug "Run" proc]
             comms <- anaEventSet es
             return comms
      Chaos es _ ->
          do addDiags [mkDiag Debug "Chaos" proc]
             comms <- anaEventSet es
             return comms
      PrefixProcess e p _ ->
          do addDiags [mkDiag Debug "Prefix" proc]
             (evComms, rcvMap) <- anaEvent e (lVars `Map.union` gVars)
             comms <- anaProcess p alpha gVars (rcvMap `Map.union` lVars)
             return (comms `Set.union` evComms)
      ExternalPrefixProcess v s p _ ->
          do addDiags [mkDiag Debug "External prefix" proc]
             checkSorts [s]
             comms <- anaProcess p alpha gVars (Map.insert v s lVars)
             return (Set.insert (CommTypeSort s) comms)
      InternalPrefixProcess v s p _ ->
          do addDiags [mkDiag Debug "Internal prefix" proc]
             checkSorts [s]
             comms <- anaProcess p alpha gVars (Map.insert v s lVars)
             return (Set.insert (CommTypeSort s) comms)
      Sequential p q _ ->
          do addDiags [mkDiag Debug "Sequential" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars Map.empty
             return (pComms `Set.union` qComms)
      ExternalChoice p q _ ->
          do addDiags [mkDiag Debug "ExternalChoice" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars lVars
             return (pComms `Set.union` qComms)
      InternalChoice p q _ ->
          do addDiags [mkDiag Debug "InternalChoice" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars lVars
             return (pComms `Set.union` qComms)
      Interleaving p q _ ->
          do addDiags [mkDiag Debug "Interleaving" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars lVars
             return (pComms `Set.union` qComms)
      SynchronousParallel p q _ ->
          do addDiags [mkDiag Debug "Synchronous" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars lVars
             return (pComms `Set.union` qComms)
      GeneralisedParallel p es q _ ->
          do addDiags [mkDiag Debug "Generalised parallel" proc]
             pComms <- anaProcess p alpha gVars lVars
             synComms <- anaEventSet es
             qComms <- anaProcess q alpha gVars lVars
             return (Set.unions [pComms, qComms, synComms])
      AlphabetisedParallel p esp esq q _ ->
          do addDiags [mkDiag Debug "Alphabetised parallel" proc]
             pComms <- anaProcess p alpha gVars lVars
             pSynComms <- anaEventSet esp
             qSynComms <- anaEventSet esq
             qComms <- anaProcess q alpha gVars lVars
             checkCommAlphaSub pSynComms pComms
             checkCommAlphaSub qSynComms qComms
             return (pComms `Set.union` qComms)
      Hiding p es _ ->
          do addDiags [mkDiag Debug "Hiding" proc]
             pComms <- anaProcess p alpha gVars lVars
             hidComms <- anaEventSet es
             return (pComms `Set.union` hidComms)
      RelationalRenaming p _ _ ->
          do addDiags [mkDiag Debug "Renaming" proc]
             -- XXX check renaming
             anaProcess p alpha gVars lVars
             return Set.empty
      ConditionalProcess _ p q _ ->
          do addDiags [mkDiag Debug "Conditional" proc]
             pComms <- anaProcess p alpha gVars lVars
             qComms <- anaProcess q alpha gVars lVars
             let fComms = Set.empty -- XXX get formula sorts here
             return (Set.unions [pComms, qComms, fComms])
      NamedProcess _ _ _ ->
          do addDiags [mkDiag Debug "Named process" proc]
             -- XXX do this
             return Set.empty

-- This next works but has useless error messages: no position
-- information, no fine-grained help as to what's causing the error.
-- XXX Fix this.
checkCommAlphaSub :: CommAlpha -> CommAlpha -> State CspSign ()
checkCommAlphaSub sub super = do
  sig <- get
  let err = "comm alphabet subset failure"
  if ((closeCspCommAlpha sig sub) `Set.isSubsetOf`
      (closeCspCommAlpha sig super))
    then do return ()
    else do addDiags [mkDiag Error err ()]
            return ()

-- Event sets

anaEventSet :: EVENT_SET -> State CspSign CommAlpha
anaEventSet (EventSet es _) = do
  sig <- get
  comms <- Monad.foldM (checkCommType sig) Set.empty es
  vds <- gets envDiags
  put sig { envDiags = vds }
  return comms

-- Events

anaEvent :: EVENT -> ProcVarMap -> State CspSign (CommAlpha, ProcVarMap)
anaEvent e vars = case e of
                    Event t _ -> anaTermEvent t vars
                    Send c t _ -> anaSendEvent c t vars
                    NonDetSend c v s _ -> anaBindingEvent c v s
                    Receive c v s _ -> anaBindingEvent c v s

anaTermEvent :: (TERM ()) -> ProcVarMap ->
                State CspSign (CommAlpha, ProcVarMap)
anaTermEvent _ _ = do
  -- XXX Need to implement computing a term's sort
  let alpha = []
  return (Set.fromList alpha, Map.empty)

anaSendEvent :: CHANNEL_NAME -> (TERM ()) -> ProcVarMap ->
                State CspSign (CommAlpha, ProcVarMap)
anaSendEvent c _ _ = do
  sig <- get
  let ext = extendedInfo sig
  case c `Map.lookup` (chans ext) of
    Nothing -> do
      addDiags [mkDiag Error "unknown channel" c]
      return (Set.empty, Map.empty)
    Just _ -> do -- XXX chanSort
      -- XXX Need to implement computing a term's sort
      -- XXX Need to check sort(t) <= chanSort
      let alpha = []
      return (Set.fromList alpha, Map.empty)

anaBindingEvent :: CHANNEL_NAME -> VAR -> SORT ->
                   State CspSign (CommAlpha, ProcVarMap)
anaBindingEvent c v s = do
  sig <- get
  let ext = extendedInfo sig
  case c `Map.lookup` (chans ext) of
    Nothing -> do
      addDiags [mkDiag Error "unknown channel" c]
      return (Set.empty, Map.empty)
    Just chanSort -> do
      if s `Set.member` (subsorts chanSort)
        then do let alpha = [CommTypeSort s
                            ,CommTypeChan (TypedChanName c s)]
                let binding = [(v, s)]
                return (Set.fromList alpha, Map.fromList binding)
        else do let err = "sort not a subsort of channel's sort"
                addDiags [mkDiag Error err s]
                return (Set.empty, Map.empty)
            where subsorts = Rel.predecessors (sortRel sig)

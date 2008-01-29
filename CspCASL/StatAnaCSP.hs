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

{- Todo:
   Most of the process and channel analysis missing.
   Sentences are completely missing.
-}

module CspCASL.StatAnaCSP where

import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

import CASL.AS_Basic_CASL (SORT, VAR)
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
    Result ds (Just ()) -- insert diags
    return (cc, mkExtSign accSig, [])

ana_BASIC_CSP :: CspBasicSpec -> State CspSign CspBasicSpec
ana_BASIC_CSP cc = do
    checkLocalTops
    chs <- anaChanDecls (channels cc)
    peqs <- anaProcItems (proc_items cc)
    return (CspBasicSpec chs peqs)

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

anaChanDecls :: [CHANNEL_DECL] -> State CspSign [CHANNEL_DECL]
anaChanDecls cs = mapM (anaChanDecl) cs

anaChanDecl :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChanDecl (ChannelDecl chanNames chanSort) = do
    checkSorts [chanSort]
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
    newChanMap <- Monad.foldM (anaChannelName chanSort)
                  oldChanMap chanNames
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }
            , envDiags = vds
            }
    return (ChannelDecl chanNames chanSort)

anaChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME ->
                    State CspSign ChanNameMap
anaChannelName s m c = do
    case Map.lookup c m of 
      Nothing -> return (Map.insert c s m) -- new channel name; insert.
      Just e -> if e == s
                  then do return m -- already declared with this sort.
                  else do let err = "channel declared with multiple sorts"
                          addDiags [mkDiag Error err c]
                          return m

anaProcItems :: [PROC_ITEM] -> State CspSign [PROC_ITEM]
anaProcItems ps = mapM (anaProcItem) ps

anaProcItem :: PROC_ITEM -> State CspSign PROC_ITEM
anaProcItem (Proc_Decl n args (ProcAlphabet cts x)) = do
    sig <- get
    let ext = extendedInfo sig
        oldProcDecls = procs ext
    newProcDecls <-
        if n `Map.member` oldProcDecls
        then do let err = "process name declared more than once"
                addDiags [mkDiag Error err n]
                return oldProcDecls
        else do -- new declation
                checkSorts args
                alpha <- Monad.foldM (checkCommType sig) Set.empty cts
                let prof = (ProcProfile args alpha)
                return (Map.insert n prof oldProcDecls)
    vds <- gets envDiags
    put sig { extendedInfo = ext {procs = newProcDecls }
            , envDiags = vds
            }
    -- XXX Should be a CommAlpha not a COMM_ALPHA here - pah!
    return (Proc_Decl n args (ProcAlphabet cts x))
anaProcItem (Proc_Eq (ParmProcname pn vs) proc) = do
    sig <- get
    let ext = extendedInfo sig
        procDecls = procs ext
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
    return (Proc_Eq (ParmProcname pn vs) proc)

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

-- Processes

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
             rcvVarMap <- anaEvent e alpha gVars lVars
             anaProcess p alpha gVars (rcvVarMap `Map.union` lVars) 
             return Set.empty
      ExternalPrefixProcess v s p _ ->
          do addDiags [mkDiag Debug "External prefix" proc]
             checkSorts [s]
             anaProcess p alpha gVars (Map.insert v s lVars)
             return Set.empty
      InternalPrefixProcess v s p _ ->
          do addDiags [mkDiag Debug "Internal prefix" proc]
             checkSorts [s]
             anaProcess p alpha gVars (Map.insert v s lVars)
             return Set.empty
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
             -- XXX check inclusions
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

anaEvent :: EVENT -> CommAlpha -> ProcVarMap -> ProcVarMap ->
            State CspSign ProcVarMap
anaEvent _ _ _ _ = return Map.empty

{-
    case e of
      Event t _ -> anaTermEvent t alpha (lVars `Map.union` gVars)
      Send c t _ -> anaSendEvent c t alpha (lVars `Map.union` gVars)
      Receive c v s _ -> anaReceiveEvent c v s alpha

anaTermEvent :: (TERM ()) -> CommAlpha -> ProcVarMap ->
                State CspSign ProcVarMap
anaTermEvent t alpha vMap = do
    addDiags [mkDiag Debug "anaTermEvent" t]
    --anaAlphaSort sort(t)
    return Map.empty

anaSendEvent :: CHANNEL_NAME -> (TERM ()) -> CommAlpha -> ProcVarMap ->
                State CspSign ProcVarMap
anaSendEvent chan t alpha vMap = return Map.empty

anaReceiveEvent :: CHANNEL_NAME -> VAR -> SORT -> CommAlpha ->
                   State CspSign ProcVarMap
anaReceiveEvent chan v s alpha = do
    sig <- get
    let ext = extendedInfo sig
    case chan `Map.lookup` (chans ext) of
      Nothing -> do addDiags [mkDiag Error "unknown channel" chan]
                    return Map.empty
      Just chanSort -> do anaAlphaChan alpha chan
                          anaAlphaSort alpha chanSort
                          if chanSort == s -- XXX possibly unnecesary?
                                           -- XXX possibly sort here
                                           --     unnecessary?
                             then return (Map.fromList [(v, s)])
                             else do let err = "wrong sort for channel"
                                     addDiags [mkDiag Error err chan]
                                     return Map.empty
                          return Map.empty

-}

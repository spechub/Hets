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
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS, PROCESS_NAME)
import CspCASL.LocalTop (Obligation(..), unmetObs)
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
                 ++ ") unfulfilled.")

anaChanDecls :: [CHANNEL_DECL] -> State CspSign [CHANNEL_DECL]
anaChanDecls cs = mapM (anaChanDecl) cs

anaChanDecl :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChanDecl cd = do
    checkSorts [(channelSort cd)]
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
        s = channelSort cd
        cns = channelNames cd
    newChanMap <- Monad.foldM (anaChannelName s) oldChanMap cns
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }
            , envDiags = vds
            }
    return cd

anaChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME ->
                    State CspSign ChanNameMap
anaChannelName s m c = do
    case Map.lookup c m of 
      Nothing -> return (Map.insert c s m) -- new channel name; insert.
      Just e -> if e == s
                  then do return m -- already declared with this sort.
                  else do let err = "channel declared with multiple sorts:"
                          addDiags [mkDiag Error err c]
                          return m

anaProcItems :: [PROC_ITEM] -> State CspSign [PROC_ITEM]
anaProcItems ps = mapM (anaProcItem) ps

anaProcItem :: PROC_ITEM -> State CspSign PROC_ITEM
anaProcItem (ProcDecl n args alpha) = do
    sig <- get
    let ext = extendedInfo sig
        oldProcDecls = procs ext
    newProcDecls <- if n `Map.member` oldProcDecls
                    then do let err = "process name declared more than once:"
                            addDiags [mkDiag Error err n]
                            return oldProcDecls
                    else anaNewProc n args alpha oldProcDecls -- new declation
    vds <- gets envDiags
    put sig { extendedInfo = ext {procs = newProcDecls }
            , envDiags = vds
            }
    return (ProcDecl n args alpha)
anaProcItem (ProcEq (ParmProcname pn vs) proc) = do
    sig <- get
    let ext = extendedInfo sig
        procDecls = procs ext
        prof = pn `Map.lookup` procDecls
    case prof of
      -- Only analyse a process if its name (and thus profile) is known
      Just pf -> do gVars <- anaProcVars pn (procArgs pf) vs
                    anaProcess proc pn gVars Map.empty
      Nothing -> do addDiags [mkDiag Error "unknown process" pn]
                    return ()
    vds <- gets envDiags
    put sig { envDiags = vds }
    return (ProcEq (ParmProcname pn vs) proc)

-- Analyse a process declaration for a new process name.
anaNewProc :: PROCESS_NAME -> PROC_ARGS -> PROC_ALPHABET ->
              ProcNameMap -> State CspSign ProcNameMap
anaNewProc n args alpha oldMap = do
    checkSorts args
    checkSorts (commSorts alpha)
    sig <- get
    let ext = extendedInfo sig
        chanMap = chans ext
    -- check channel names are known
    addDiags $ concatMap (anaProcChan chanMap) (commChans alpha)
    -- Build process profile to return
    let chan_sorts = Maybe.catMaybes (map (flip Map.lookup chanMap)
                                              (commChans alpha))
        alpha_sorts = Set.fromList ((commSorts alpha) ++ chan_sorts)
        alpha_chans = Set.fromList (commChans alpha)
        prof = (ProcProfile args (ProcAlpha alpha_sorts alpha_chans))
    return (Map.insert n prof oldMap)

anaProcChan :: ChanNameMap -> CHANNEL_NAME -> [Diagnosis]
anaProcChan cm c =
    if c `Map.member` cm then [] else [mkDiag Error "unknown channel" c]

type ProcVarMap = Map.Map VAR SORT

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

anaProcess :: PROCESS -> PROCESS_NAME -> ProcVarMap -> ProcVarMap -> State CspSign ()
anaProcess p pn gVars lVars = return ()

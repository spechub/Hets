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

import CASL.AS_Basic_CASL (SORT)
import CASL.Sign
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)
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
    chs <- anaChannels (channels cc)
    peqs <- anaProcesses (proc_items cc)
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

anaChannels :: [CHANNEL_DECL] -> State CspSign [CHANNEL_DECL]
anaChannels cs = mapM (anaChannel) cs

anaChannel :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChannel cd = do
    checkSorts [(channelSort cd)]
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
        s = channelSort cd
        cns = channelNames cd
    newChanMap <- Monad.foldM (checkChannelName s) oldChanMap cns
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }
            , envDiags = vds
            }
    return cd

checkChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME ->
                    State CspSign ChanNameMap
checkChannelName s m c = do
    case Map.lookup c m of 
      Nothing -> return (Map.insert c s m) -- new channel name; insert.
      Just e -> if e == s
                  then do return m -- already declared with this sort.
                  else do let err = "channel declared with multiple sorts:"
                          addDiags [mkDiag Error err c]
                          return m

anaProcesses :: [PROC_ITEM] -> State CspSign [PROC_ITEM]
anaProcesses ps = mapM (anaProcess) ps

anaProcess :: PROC_ITEM -> State CspSign PROC_ITEM
anaProcess (ProcDecl n args alpha) = do
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
anaProcess (ProcEq ppn proc) = return (ProcEq ppn proc)

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
    addDiags $ concatMap (knownChan chanMap) (commChans alpha)
    -- Build process profile to return
    let chan_sorts = Maybe.catMaybes (map (flip Map.lookup chanMap)
                                              (commChans alpha))
        alpha_sorts = Set.fromList ((commSorts alpha) ++ chan_sorts)
        alpha_chans = Set.fromList (commChans alpha)
        prof = (ProcProfile args (ProcAlpha alpha_sorts alpha_chans))
    return (Map.insert n prof oldMap)

knownChan :: ChanNameMap -> CHANNEL_NAME -> [Diagnosis]
knownChan cm c =
    if c `Map.member` cm then [] else [mkDiag Error "unknown channel" c]

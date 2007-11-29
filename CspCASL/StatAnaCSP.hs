{- |
Module      :  $Id$
Description :  static analysis for CspCASL
Copyright   :  (c) Markus Roggenbach, Till Mossakowski, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

static analysis for CSP-CASL

-}

{- todo:
   most of the process and channel analysis missing

   sentences are completely missing:
   use equation systems of processes, like:

   spec hugo =
     data ...
     channel ...
     process A = a->A
     process P = ...A...Q...
             Q = ...P....
             R = a->P
     reveal R

reveal R should keep CASL data part, and reveal process R

-}

module CspCASL.StatAnaCSP where

import CASL.Sign
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.Id
import qualified Data.Map as Map
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
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
    chs' <- anaChannels (channels cc)
    peqs' <- anaProcesses (proc_items cc)
    return (CspBasicSpec chs' peqs')

-- | Check CspCASL signature for local top elements in subsorts.
checkLocalTops :: State CspSign ()
checkLocalTops = do
    sig <- get
    put sig
    addDiags [mkDiag Warning "Test warning" ()]
    return ()

anaChannels :: [CHANNEL_DECL] -> State CspSign [CHANNEL_DECL]
anaChannels cs = mapM (anaChannel) cs
                 --fmap Channel_items $ mapM (anaChannel) cs

anaChannel :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChannel c = do
    checkSorts [(channelSort c)]
    sig <- get
    let ext = extendedInfo sig
        oldchn = chans ext
    -- test for double declaration with different sorts should be added
    let ins m n = Map.insert (mkId [n]) (channelSort c) m
    put sig { extendedInfo = ext { chans = foldl ins oldchn [] } }
    return c

anaProcesses :: [PROC_ITEM] -> State CspSign [PROC_ITEM]
anaProcesses ps = return ps




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

import qualified Control.Monad as Monad
import qualified Data.Map as Map

import CASL.AS_Basic_CASL (SORT)
import CASL.Sign
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME)
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
    where msg = ("Local top element obligation ("
                 ++ (show x) ++ "<" ++ (show y) ++ "," ++ (show z)
                 ++ ") unfulfilled.")

anaChannels :: [CHANNEL_DECL] -> State CspSign [CHANNEL_DECL]
anaChannels cs = mapM (anaChannel) cs

anaChannel :: CHANNEL_DECL -> State CspSign CHANNEL_DECL
anaChannel cDecl = do
    checkSorts [(channelSort cDecl)]
    sig <- get
    let ext = extendedInfo sig
    newChanMap <- checkChannelNames (chans ext) cDecl
    addDiags [mkDiag Debug ("newChanMap " ++ (show (newChanMap))) ()]
    vds <- gets envDiags
    put sig { extendedInfo = ext { chans = newChanMap }, envDiags = vds }
    return cDecl

checkChannelNames :: ChanNameMap -> CHANNEL_DECL -> State CspSign ChanNameMap
checkChannelNames old cDecl = Monad.foldM (checkChannelName s) old cs
    where s = (channelSort cDecl)
          cs = (channelNames cDecl)

checkChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME -> State CspSign ChanNameMap
checkChannelName s m c = do
    addDiags [mkDiag Debug ("inCheckChannelName: " ++ (show m)) c ]
    case Map.lookup c m of 
      Nothing -> do addDiags [mkDiag Debug "Not already there" c]
                    return (Map.insert c s m)
      Just e -> if e == s
                  then do addDiags [mkDiag Debug "Channel already declared, same sort" c]
                          return m
                  else do addDiags [mkDiag Error "Channel already declared" c]
                          return m

anaProcesses :: [PROC_ITEM] -> State CspSign [PROC_ITEM]
anaProcesses ps = return ps




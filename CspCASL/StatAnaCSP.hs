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

-- This is a very null analysis function, returning as it does
-- essentially unchanged data.
basicAnalysisCspCASL :: (CspBasicSpec, CSPSign, GlobalAnnos)
        -> Result (CspBasicSpec, ExtSign CSPSign (), [Named ()])
basicAnalysisCspCASL (cc, sigma, _ga) =
  do let (_, accSig) =
             runState (ana_BASIC_CSP ((channels cc), (proc_items cc))) sigma
         ds = reverse $ envDiags accSig
     Result ds (Just ()) -- insert diags
     return (CspBasicSpec (channels cc) (proc_items cc),
             mkExtSign accSig, [])

-- | the main CspCASL analysis function
ana_BASIC_CSP :: ([CHANNEL], [PROC_ITEM])
         -> State CSPSign ([CHANNEL], [PROC_ITEM])
ana_BASIC_CSP (chs, peqs) = do
   chs' <- anaChannels chs
   peqs' <- anaProcesses peqs
   return (chs', peqs')

anaChannels :: [CHANNEL] -> State CSPSign [CHANNEL]
anaChannels cs = mapM (anaChannel) cs
  --fmap Channel_items $ mapM (anaChannel) cs

anaChannel :: CHANNEL -> State CSPSign CHANNEL
anaChannel c = do
  checkSorts [(channelSort c)]
  sig <- get
  let ext = extendedInfo sig
      oldchn = channelNames' ext
  -- test for double declaration with different sorts should be added
  let ins m n = Map.insert (mkId [n]) (channelSort c) m
  put sig { extendedInfo = ext { channelNames' = foldl ins oldchn [] } }
  return c

anaProcesses :: [PROC_ITEM] -> State CSPSign [PROC_ITEM]
anaProcesses ps = return ps




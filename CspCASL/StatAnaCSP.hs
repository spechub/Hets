{- |
Module      :  $Header$
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
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

import CspCASL.AS_CSP_CASL
import CspCASL.SignCSP
import CASL.Sign
import CASL.StaticAna
import CASL.MixfixParser
import CASL.Overload
import Common.Result
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import Common.Lib.State
import Common.PrettyPrint
import Common.Id
import Common.AS_Annotation

-- | static analysis for standalone tool
statAna :: C3PO -> Result CSPSign
statAna (Named_c3po (Named_csp_casl_spec _ sp)) =
  statBasicSpec sp

statAna (C3po sp) =
  statBasicSpec sp


statBasicSpec :: CSP_CASL_C_SPEC -> Result CSPSign
statBasicSpec (Csp_casl_c_spec sp ch p) =
  do (sp',sig,_,_) <- basicAnalysis 
                               (const $ const return) 
                               (const $ const return)
                               (const $ const return)
                               emptyMix
                               diffCSPAddSign
                               (sp, emptyCSPSign, emptyGlobalAnnos)
     let (_, accSig) = runState (ana_BASIC_CSP (ch,p)) sig
     return accSig
        
-- | static analysis for Hets
basicAnalysisCspCASL :: (Basic_CSP_CASL_C_SPEC,CSPSign,GlobalAnnos) 
        -> Result (Basic_CSP_CASL_C_SPEC,CSPSign,CSPSign,[Named ()])
basicAnalysisCspCASL (Basic_csp_casl_c_spec ch p,sigma,ga) =
  do let ((ch',p'), accSig) = runState (ana_BASIC_CSP (ch,p)) sigma
         diffSig = diffCSPSign accSig sigma
         ds = reverse $ envDiags accSig
     Result ds (Just ()) -- insert diags
     return (Basic_csp_casl_c_spec ch' p',diffSig,accSig,[])

-- | the main CspCASL analysis function
ana_BASIC_CSP :: (CHANNEL_DECL, PROCESS_DEFN) 
         -> State CSPSign (CHANNEL_DECL, PROCESS_DEFN)
ana_BASIC_CSP (ch, p) = do
   ch' <- anaChannels ch
   p' <- anaProcesses p 
   return (ch',p') 

anaChannels (Channel_items cits) = 
  fmap Channel_items $ mapM (anaChannel) cits

anaChannel :: CHANNEL_ITEM -> State CSPSign CHANNEL_ITEM
anaChannel chdecl@(Channel_decl newnames s) = do
  checkSorts [s]
  sig <- get
  let ext = extendedInfo sig
      oldchn = channelNames ext
  -- test for double declaration with different sorts should be added
  let ins m n = Map.insert (mkId [n]) s m
  put sig { extendedInfo = ext { channelNames = foldl ins oldchn newnames } }
  return chdecl  


anaProcesses p =
  return p

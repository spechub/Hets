{- |
Module      :  $Header$
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable


  static analysis for CSP-CASL

-}

{- todo:
   equation systems of processes 
   
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
import CASL.Overload
import Common.Result
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import Common.Lib.State
import Common.PrettyPrint
import Common.Id

statAna :: C3PO -> Result CSPSign
statAna (Named_c3po (Named_csp_casl_spec _ sp)) =
  statBasicSpec sp

statAna (C3po sp) =
  statBasicSpec sp

statBasicSpec :: CSP_CASL_C_SPEC -> Result CSPSign
statBasicSpec (Csp_casl_c_spec sp ch p) =
  do (sp',sig,_,_) <- basicAnalysis (const $ const return) 
			       (const return)
			       (const return) (sp, emptyCSPSign, emptyGlobalAnnos)
     let (_, accSig) = runState (ana_BASIC_CSP (ch,p)) sig
     return accSig
	

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

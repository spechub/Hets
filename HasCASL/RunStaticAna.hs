
{- HetCATS/HasCASL/RunStaticAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse and call static analysis
-}


module RunStaticAna where

import AnnoState
import Le
import AsToLe(anaBasicSpec)
import ParseItem(basicSpec)
import MonadState

anaParser :: AParser Env
anaParser = do b <- basicSpec
	       return $ snd $ (runState (anaBasicSpec b)) initialEnv


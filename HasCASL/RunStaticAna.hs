
{- HetCATS/HasCASL/RunStaticAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse and call static analysis
-}


module RunStaticAna where

import Le
import AsToLe(anaBasicSpec)
import ParseItem(basicSpec)
import Parsec
import MonadState

anaParser :: Parser Env
anaParser = do b <- basicSpec
	       return $ snd $ (runState (anaBasicSpec b)) initialEnv


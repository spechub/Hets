
{- HetCATS/HasCASL/RunStaticAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse and call static analysis
-}


module HasCASL.RunStaticAna where

import Common.AnnoState
import HasCASL.Le
import HasCASL.AsToLe(anaBasicSpec)
import HasCASL.ParseItem(basicSpec)
import Control.Monad.State

anaParser :: AParser Env
anaParser = do b <- basicSpec
	       return $ snd $ (runState (anaBasicSpec b)) initialEnv


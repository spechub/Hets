{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   parse and call static analysis
-}


module HasCASL.RunStaticAna where

import Common.AnnoState
import Common.GlobalAnnotations
import HasCASL.Le
import HasCASL.AsToLe(anaBasicSpec)
import HasCASL.ParseItem(basicSpec)
import Common.Lib.State

anaParser :: GlobalAnnos -> AParser Env
anaParser ga = do b <- basicSpec
		  return $ snd $ (runState (anaBasicSpec ga b)) initialEnv


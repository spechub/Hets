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
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.AsToLe(anaBasicSpec)
import HasCASL.ParseItem(basicSpec)
import Common.Lib.State
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.RunParsers

anaParser :: StringParser
anaParser ga = do b <- aParse basicSpec
		  let (a, e) = runState (anaBasicSpec ga b) initialEnv
                  return $ show (printText0 ga a $$ printText0 ga e)


{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.DGTranslation where

--  data structure
import Logic.Grothendieck
import Static.DevGraph
import Syntax.AS_Library
import Common.Result
import qualified Common.Lib.Map as Map

-- import Static.DGTranslation
import Static.DGTranslation
import Comorphisms.PCFOL2CFOL

{-
dg_translation_GUI :: (LIB_NAME, LibEnv) 
                   -> AnyComorphism 
                   ->IO (LIB_NAME, LibEnv)
dg_translation_GUI (ln, libenv) comorphism = 
    do newgc <- case Map.lookup ln libenv of
                  Just gc -> trans gc comorphism
                  Nothing -> error "......"
       let newLibenv = Map.update (\_ -> Just newgc) ln libenv
       return (ln, newLibenv)
-}

trans :: GlobalContext -> AnyComorphism -> IO GlobalContext
trans gc comorphism= do
    case dg_translation gc comorphism of
      Result diagsT maybeGC ->
          do putStrLn $ show diagsT
             case maybeGC of
               Just gc' -> return gc'
               Nothing  -> return gc  


trans_PCFOL2CFOL gc = trans gc (Comorphism PCFOL2CFOL)


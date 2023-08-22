{- |
Module      :  ./Common/testxupdate.hs
Description :  analyse xml update input
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Main (main) where

import Common.XUpdate
import Common.Result

main :: IO ()
main = do
  str <- getContents
  let Result ds m = anaXUpdates str
  case m of
    Nothing -> printDiags 1 ds
    Just cs -> mapM_ print cs

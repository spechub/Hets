{- |
Module      :  $Header$
Description :  wrapper for simple http
Copyright   :  (c) Christian Maeder 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (uses package HTTP)

-}

module Common.Http where

import Common.Utils

import System.Exit

loadFromUri :: String -> IO (Either String String)
loadFromUri str = do
  (code, out, err) <- executeProcess "wget"
     ["--no-check-certificate", "-O", "-", str] ""
  return $ case code of
    ExitSuccess -> Right out
    _ -> Left err

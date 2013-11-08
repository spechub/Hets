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

import Network.HTTP
import Network.Stream

loadFromUri :: String -> IO (Result (Response String))
loadFromUri =
  simpleHTTP . replaceHeader HdrAccept "text/plain" . getRequest

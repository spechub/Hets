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
import Network.Browser

loadFromUri :: String -> IO (Result (Response String))
loadFromUri str = fmap (Right . snd) . browse $ do
    setOutHandler . const $ return ()
    setAllowRedirects True
    request . replaceHeader HdrAccept "text/plain" $ getRequest str

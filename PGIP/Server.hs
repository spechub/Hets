{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server where

import Driver.Options

import Network.Wai.Handler.SimpleServer
import Network.Wai

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

hetsServer :: HetcatsOpts -> IO ()
hetsServer _opts = run 8000 $ \ re -> do
  s <- getSource (requestBody re)
  return $ Response status200 [] $ ResponseLBS $ BS.pack
    $ unlines $
    [ "RequestMethod: " ++ B8.unpack (requestMethod re)
    , "HTTP/" ++ B8.unpack (httpVersion re)
    , "PathInfo: " ++ B8.unpack (pathInfo re)
    , "QueryString: " ++ B8.unpack (queryString re)
    , "Server: " ++ B8.unpack (serverName re) ++ ":" ++ show (serverPort re)
    , "Headers:" ]
    ++ map (\ (k, v) -> "  " ++ B8.unpack (ciOriginal k)
            ++ ": " ++ B8.unpack v) (requestHeaders re)
    ++
    [ if isSecure re then "secure https" else "not secure"
    , "Body: " ++ s
    , "RemoteHost: " ++ B8.unpack (remoteHost re)]

getSource :: Source -> IO String
getSource s = do
  mp <- runSource s
  case mp of
    Nothing -> return ""
    Just (bs, r) -> do
      rs <- getSource r
      return $ B8.unpack bs ++ rs

{- |
Module      :  ./PGIP/RequestCache.hs
Description :  hets server request cache

License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Daniel Hackbarth <da_ha@uni-bremen.de>
-}

module PGIP.RequestCache where

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Text as T

import Network.HTTP.Types.Method
import Network.Wai.Internal

-- | Holds all necessary informations for caching a request
data RequestMapKey = RequestMapKey {
  -- | The used request method.
    requestMethod' :: Method
  -- | The request URL without the server and port.
  , pathInfo' :: [T.Text]
  -- | The send request body.
  , requestBody' :: BS.ByteString
  }
  deriving (Show, Ord, Eq)

-- | Returns a new request cache.
createNewRequestCache :: IO (IORef (Map.Map RequestMapKey Response))
createNewRequestCache =
  newIORef (Map.empty :: Map.Map RequestMapKey Response)

-- | Update the request cache with a new request/response pair.
updateCache :: RequestMapKey -> Response -> IORef ((Map.Map RequestMapKey Response)) -> IO ()
updateCache requestKey response cacheRef= do
  cachedRequestsResponsesMap <- readIORef cacheRef
  let cacheMap = Map.insert requestKey response cachedRequestsResponsesMap
  writeIORef cacheRef cacheMap

-- | Checks the request cache for a request that could already be cached.
-- Returns the cached response or Nothing if the request is not cached.
lookupCache :: RequestMapKey -> IORef ((Map.Map RequestMapKey Response)) -> IO (Maybe Response)
lookupCache cacheKey cacheRef = do
  cachedRequestsResponsesMap <- readIORef cacheRef
  return $ Map.lookup cacheKey cachedRequestsResponsesMap

-- | Converts a given request to a key that can be used for a request cache.
-- The original request body needs to be passed too because in the original request
-- the request body is already consumed.
convertRequestToMapKey :: Request -> BS.ByteString -> IO RequestMapKey
convertRequestToMapKey request requestBodyBS = do
  return $ RequestMapKey (requestMethod request) (pathInfo request) requestBodyBS

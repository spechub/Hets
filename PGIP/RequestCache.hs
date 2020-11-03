{-# LANGUAGE DeriveGeneric #-}

{- |
Module      :  ./PGIP/RequestCache.hs
Description :  hets server request cache

License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Daniel Hackbarth <da_ha@uni-bremen.de>
-}

module PGIP.RequestCache where

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.IORef
import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Network.HTTP.Types.Method
import Network.Wai.Internal

import GHC.Generics (Generic)
import Data.Hashable

-- | Holds all necessary informations for caching a request
data RequestMapKey = RequestMapKey {
  -- | The used request method.
    requestMethod' :: Method
  -- | The request URL without the server and port.
  , pathInfo' :: [T.Text]
  -- | The send request body.
  , requestBody' :: BS.ByteString
  }
  deriving (Show, Ord, Eq, Generic)

instance Hashable RequestMapKey

type RequestCacheMap = Map.HashMap RequestMapKey Response

-- | Returns a new request cache.
createNewRequestCache :: IO (IORef (RequestCacheMap))
createNewRequestCache =
  newIORef (Map.empty :: RequestCacheMap)

-- | Update the request cache by first building the key and then perform the update
updateCache :: IORef (BS.ByteString) -> Request -> Response -> IORef ((RequestCacheMap)) -> IO ()
updateCache requestBodyRef request response cacheMap = do
  requestBodyBS <- readIORef requestBodyRef
  requestKey <- convertRequestToMapKey request requestBodyBS
  updateCacheWithKey requestKey response cacheMap

-- | Update the request cache with a new request/response pair.
updateCacheWithKey :: RequestMapKey -> Response -> IORef ((RequestCacheMap)) -> IO ()
updateCacheWithKey requestKey response cacheRef= do
  cachedRequestsResponsesMap <- readIORef cacheRef
  let cacheMap = Map.insert requestKey response cachedRequestsResponsesMap
  atomicWriteIORef cacheRef cacheMap

-- | Checks the request cache for a request that could already be cached.
-- Returns the cached response or Nothing if the request is not cached.
lookupCache :: RequestMapKey -> IORef ((RequestCacheMap)) -> IO (Maybe Response)
lookupCache cacheKey cacheRef = do
  cachedRequestsResponsesMap <- readIORef cacheRef
  return $ Map.lookup cacheKey cachedRequestsResponsesMap

-- | Converts a given request to a key that can be used for a request cache.
-- The original request body needs to be passed too because in the original request
-- the request body is already consumed.
convertRequestToMapKey :: Request -> BS.ByteString -> IO RequestMapKey
convertRequestToMapKey request requestBodyBS = do
  return $ RequestMapKey (requestMethod request) (pathInfo request) requestBodyBS

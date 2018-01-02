{-# LANGUAGE OverloadedStrings #-}
{- |
Module      :  ./Common/Http.hs
Description :  wrapper for simple http
Copyright   :  (c) Christian Maeder 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (uses package HTTP)

-}

module Common.Http where

import Driver.Options

import Control.Exception (try)
import qualified Data.ByteString.Lazy.Char8 as LChar8
import qualified Data.ByteString.Char8 as Char8
import qualified Data.CaseInsensitive as CI (mk)
import Data.Char (isSpace)
import Network.Connection (TLSSettings(..))
import Network.HTTP.Client
import Network.HTTP.Client.TLS
import Network.HTTP.Types (statusCode)

loadFromUri :: HetcatsOpts -> String -> IO (Either String String)
loadFromUri opts uri = do
  manager <-
    if disableCertificateVerification opts
    then newManager noVerifyTlsManagerSettings
    else newManager tlsManagerSettings
  initialRequest <- parseRequest uri
  let additionalHeaders =
        map ((\ (header, value) ->
               (CI.mk $ Char8.pack header,
                Char8.pack $ dropWhile isSpace $ tail value)) .
             break (== ':')) $ httpRequestHeaders opts
  let request = initialRequest
        { requestHeaders = ("Accept", "*/*; q=0.1, text/plain")
                             : additionalHeaders }
  eResponse <- try $ httpLbs request manager
  case eResponse of
    Left err ->
      case err :: HttpException of
        HttpExceptionRequest _ exceptionContent ->
          return $ Left
            ("Failed to load " ++ show uri ++ ": " ++ show exceptionContent)
        InvalidUrlException invalidUrl reason ->
          return $ Left ("Failed to load " ++ show invalidUrl ++ ": " ++ reason)
    Right response ->
      let status = statusCode $ responseStatus response in
      return $ if 400 <= status
               then Left ("Failed to load " ++ show uri ++ ": HTTP status code "
                          ++ show status)
               else Right $ LChar8.unpack $ responseBody response

noVerifyTlsManagerSettings :: ManagerSettings
noVerifyTlsManagerSettings = mkManagerSettings noVerifyTlsSettings Nothing

noVerifyTlsSettings :: TLSSettings
noVerifyTlsSettings =
  TLSSettingsSimple { settingDisableCertificateValidation = True
                    , settingDisableSession = True
                    , settingUseServerName = False
                    }

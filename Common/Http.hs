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
import qualified Data.ByteString.Lazy.Char8 as Char8
import Network.Connection (TLSSettings(..))
import Network.HTTP.Client
import Network.HTTP.Client.TLS

loadFromUri :: HetcatsOpts -> String -> IO (Either String String)
loadFromUri opts uri = do
  manager <-
    if disableCertificateVerification opts
    then newManager noVerifyTlsManagerSettings
    else newManager tlsManagerSettings
  initialRequest <- parseRequest uri
  let request = initialRequest
        { requestHeaders = [ ("Accept", "*/*; q=0.1, text/plain") ]}
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
      return $ Right $ Char8.unpack $ responseBody response

noVerifyTlsManagerSettings :: ManagerSettings
noVerifyTlsManagerSettings = mkManagerSettings noVerifyTlsSettings Nothing

noVerifyTlsSettings :: TLSSettings
noVerifyTlsSettings =
  TLSSettingsSimple { settingDisableCertificateValidation = True
                    , settingDisableSession = True
                    , settingUseServerName = False
                    }

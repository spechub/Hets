{-# LANGUAGE TemplateHaskell #-}

module PGIP.Server.WebAssets ( hetsCss
                             , semanticUiCss
                             , semanticUiJs
                             , jQueryJs
                             ) where

import Data.ByteString (unpack)
import Data.Char (chr)
import Data.FileEmbed

hetsCss :: String
hetsCss =
  map (chr . fromEnum) $ unpack $ $(embedFile "PGIP/assets/hets.css")

semanticUiCss :: String
semanticUiCss =
  map (chr . fromEnum) $ unpack $ $(embedFile "PGIP/assets/semantic.min-2.2.13.css")

semanticUiJs :: String
semanticUiJs =
  map (chr . fromEnum) $ unpack $ $(embedFile "PGIP/assets/semantic.min-2.2.13.js")

jQueryJs :: String
jQueryJs =
  map (chr . fromEnum) $ unpack $ $(embedFile "PGIP/assets/jquery-3.2.1.min.js")

{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.Output.Translations
  ( formatTranslations
  ) where

import PGIP.Output.Formatting
import PGIP.Output.Mime

import Logic.Comorphism (AnyComorphism)
import Proofs.AbstractState (G_prover)

import Common.Json (ppJson, asJson)
import Common.ToXml (asXml)
import Common.Utils

import Text.XML.Light (ppTopElement)

import Data.Data

type TranslationsFormatter = [(G_prover, AnyComorphism)] -> (String, String)

formatTranslations :: Maybe String -> TranslationsFormatter
formatTranslations format comorphisms = case format of
  Just "json" -> formatAsJSON
  _ -> formatAsXML
  where
  convertedTranslations :: Translations
  convertedTranslations = Translations
    { translations = nubOrd $ map (showComorph . snd) comorphisms }

  formatAsJSON :: (String, String)
  formatAsJSON = (jsonC, ppJson $ asJson convertedTranslations)

  formatAsXML :: (String, String)
  formatAsXML = (xmlC, ppTopElement $ asXml convertedTranslations)

data Translations = Translations
  { translations :: [String]
  } deriving (Show, Typeable, Data)

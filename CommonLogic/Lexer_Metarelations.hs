{- |
Module      :  $Header$
Description :  Parser of common logic interchange format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interchange format
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Lexer_Metarelations where

import Common.Id as Id
import Common.Lexer as Lexer

import Text.ParserCombinators.Parsec as Parsec

-- Parsers
tokParserFromString :: String -> CharParser st Id.Token
tokParserFromString s = Lexer.pToken $ string s

relativeInterpretsKey :: CharParser st Id.Token
relativeInterpretsKey = tokParserFromString relativeInterpretsS

definablyInterpretsKey :: CharParser st Id.Token
definablyInterpretsKey = tokParserFromString definablyInterpretsS

faithfullyInterpretsKey :: CharParser st Id.Token
faithfullyInterpretsKey = tokParserFromString faithfullyInterpretsS

definablyEquivalentKey :: CharParser st Id.Token
definablyEquivalentKey = tokParserFromString definablyEquivalentS

nonconservativeExtensionKey :: CharParser st Id.Token
nonconservativeExtensionKey = tokParserFromString nonconservativeExtensionS

conservativeExtensionKey :: CharParser st Id.Token
conservativeExtensionKey = tokParserFromString conservativeExtensionS

-- Keywords
relativeInterpretsS :: String
relativeInterpretsS = "relative-interprets"

definablyInterpretsS :: String
definablyInterpretsS = "definably-interprets"

faithfullyInterpretsS :: String
faithfullyInterpretsS = "faithfully-interprets"

definablyEquivalentS :: String
definablyEquivalentS = "definably-equivalent"

nonconservativeExtensionS :: String
nonconservativeExtensionS = "nonconservative-extension"

conservativeExtensionS :: String
conservativeExtensionS = "conservative-extension"

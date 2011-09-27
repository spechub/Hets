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

import CommonLogic.Lexer_CLIF

import Common.Id as Id
import Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec

-- Parser Keywords
relativeInterpretsKey :: CharParser st Id.Token
relativeInterpretsKey = Lexer.pToken $ string relativeInterpretsS

nonconservativeExtensionKey :: CharParser st Id.Token
nonconservativeExtensionKey = Lexer.pToken $ string nonconservativeExtensionS

relativeInterpretsS :: String
relativeInterpretsS = "relative-interprets"

nonconservativeExtensionS :: String
nonconservativeExtensionS = "nonconservative-extension"

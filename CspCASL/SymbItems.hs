{- |
Module      :  $Header$
Description :  syntactic csp-casl symbols
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CspCASL.SymbItems where

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Print_CspCASL

import CASL.AS_Basic_CASL
import CASL.SymbolParser
import CASL.ToDoc ()

import Common.Doc hiding (braces)
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.Token

import Text.ParserCombinators.Parsec

import Control.Monad

import qualified Data.Set as Set

data CspSymbItems = CspSymbItems CspSymbKind [CspSymb]
  deriving (Show, Eq)

data CspSymbMapItems = CspSymbMapItems CspSymbKind [CspSymbMap]
  deriving (Show, Eq)

data CspSymbKind = CaslKind SYMB_KIND | ProcessKind | ChannelKind
  deriving (Show, Eq, Ord)

data CspSymb = CspSymb Id (Maybe CspType)
  deriving (Show, Eq)

-- for channels with sorts we may re-use A_type that is ambiguous
data CspType = CaslType TYPE | ProcType ProcProfile
  deriving (Show, Eq)

data CspSymbMap = CspSymbMap CspSymb (Maybe CspSymb)
  deriving (Show, Eq)

instance Pretty CspSymbKind where
  pretty k = case k of
    CaslKind c -> pretty c
    ProcessKind -> keyword processS
    ChannelKind -> keyword channelS

instance Pretty CspType where
  pretty t = case t of
    CaslType c -> colon <> pretty c
    ProcType p -> printProcProfile p

instance Pretty CspSymb where
  pretty (CspSymb i ms) = pretty i <+> pretty ms

instance Pretty CspSymbMap where
  pretty (CspSymbMap s ms) = pretty s <+> case ms of
    Nothing -> empty
    Just t -> mapsto <+> pretty t

instance Pretty CspSymbItems where
  pretty (CspSymbItems k syms) = pretty k <+> ppWithCommas syms

instance Pretty CspSymbMapItems where
  pretty (CspSymbMapItems k syms) = pretty k <+> ppWithCommas syms

sortList :: [String] -> GenParser Char st [SORT]
sortList = commaSep1 . sortId

bracedList :: [String] -> GenParser Char st [SORT]
bracedList = braces . sortList

toAlphaComm :: [SORT] -> CommAlpha
toAlphaComm = Set.fromList . map CommTypeSort

-- | parsing a possibly qualified identifier
cspSymb :: [String] -> GenParser Char st CspSymb
cspSymb ks =
    do i <- parseId ks
       do
         _ <- colonST
         t <- fmap CaslType (opOrPredType ks) <|>
            fmap (ProcType . ProcProfile [] . toAlphaComm) (bracedList ks)
         return $ CspSymb i $ Just t
        <|> do
         ts <- between oParenT cParenT $ commaSep1 $ sortId ks
         _ <- pToken $ toKey colonS
         cs <- single (sortId ks) <|> bracedList ks
         return $ CspSymb i $ Just $ ProcType $ ProcProfile ts
           $ toAlphaComm cs
        <|> return (CspSymb i Nothing)

-- | parsing one symbol or a mapping of one to second symbol
cspSymbMap :: [String] -> GenParser Char st CspSymbMap
cspSymbMap ks = liftM2 CspSymbMap (cspSymb ks) $ optionMaybe
  $ pToken (toKey mapsTo) >> cspSymb ks

-- | parse a kind keyword
cspSymbKind :: GenParser Char st CspSymbKind
cspSymbKind =
  fmap (const ChannelKind) (pluralKeyword channelS)
  <|> fmap (const ProcessKind) (pToken $ toKey processS)
  <|> fmap (CaslKind . fst) symbKind

-- | parse a comma separated list of symbols
cspSymbs :: [String] -> GenParser Char st [CspSymb]
cspSymbs ks =
    do s <- cspSymb ks
       do
         _ <- commaT `followedWith` parseId ks
         is <- cspSymbs ks
         return $ s : is
        <|> return [s]

{- | Parse a possible kinded list of comma separated CspCASL symbols.
     The argument is a list of keywords to avoid as identifiers. -}
cspSymbItems :: [String] -> GenParser Char st CspSymbItems
cspSymbItems ks = fmap (CspSymbItems $ CaslKind Implicit) (cspSymbs ks) <|> do
    k <- cspSymbKind
    fmap (CspSymbItems k) (cspSymbs ks)

-- | parse a comma separated list of symbols
cspSymbMaps :: [String] -> GenParser Char st [CspSymbMap]
cspSymbMaps ks =
    do s <- cspSymbMap ks
       do
         _ <- commaT `followedWith` parseId ks
         is <- cspSymbMaps ks
         return $ s : is
        <|> return [s]

-- | parse a possible kinded list of CspCASL symbol mappings
cspSymbMapItems :: [String] -> GenParser Char st CspSymbMapItems
cspSymbMapItems ks = fmap (CspSymbMapItems $ CaslKind Implicit) (cspSymbMaps ks)
  <|> do
    k <- cspSymbKind
    fmap (CspSymbMapItems k) (cspSymbMaps ks)

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
import CspCASL.Parse_CspCASL_Process

import CASL.AS_Basic_CASL
import CASL.SymbolParser
import CASL.ToDoc

import Common.AnnoState
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

pluralCspSympKind :: CspSymbKind -> [a] -> Doc
pluralCspSympKind k l = case k of
    CaslKind c -> case c of
      Implicit -> empty
      _ -> keyword $ pluralS_symb_list c l
    ProcessKind -> keyword processS
    ChannelKind -> keyword $ channelS ++ appendS l

instance Pretty CspSymbKind where
  pretty k = pluralCspSympKind k [()]

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
  pretty (CspSymbItems k l) = pluralCspSympKind k l <+> ppWithCommas l

instance Pretty CspSymbMapItems where
  pretty (CspSymbMapItems k l) = pluralCspSympKind k l <+> ppWithCommas l

commType :: AParser st CommType
commType = do
  s <- cspSortId
  do
    colonT
    r <- cspSortId
    if isSimpleId s
      then return $ CommTypeChan $ TypedChanName (idToSimpleId s) r
      else unexpected $ "sort " ++ show s
   <|> return (CommTypeSort s)

bracedList :: AParser st [CommType]
bracedList = braces $ commaSep1 commType

commAlpha :: AParser st CommAlpha
commAlpha = fmap Set.fromList $ single commType <|> bracedList

-- | parsing a possibly qualified identifier
cspSymb :: AParser st CspSymb
cspSymb =
    do i <- parseCspId
       do
         _ <- colonST
         t <- fmap CaslType (opOrPredType cspKeywords) <|>
            fmap (ProcType . ProcProfile []) commAlpha
         return $ CspSymb i $ Just t
        <|> do
         ts <- parenList cspSortId
         colonT
         cs <- commAlpha
         return $ CspSymb i $ Just $ ProcType $ ProcProfile ts cs
        <|> return (CspSymb i Nothing)

-- | parsing one symbol or a mapping of one to second symbol
cspSymbMap :: AParser st CspSymbMap
cspSymbMap = liftM2 CspSymbMap cspSymb $ optionMaybe
  $ asKey mapsTo >> optional cspSymbKind >> cspSymb

-- | parse a kind keyword
cspSymbKind :: AParser st CspSymbKind
cspSymbKind =
  fmap (const ChannelKind) (pluralKeyword channelS)
  <|> fmap (const ProcessKind) (asKey processS)
  <|> fmap (CaslKind . fst) symbKind

-- | parse a comma separated list of symbols
cspSymbs :: AParser st [CspSymb]
cspSymbs =
    do s <- cspSymb
       do
         _ <- commaT `followedWith` parseCspId
         is <- cspSymbs
         return $ s : is
        <|> return [s]

{- | Parse a possible kinded list of comma separated CspCASL symbols.
     The argument is a list of keywords to avoid as identifiers. -}
cspSymbItems :: AParser st CspSymbItems
cspSymbItems = fmap (CspSymbItems $ CaslKind Implicit) cspSymbs <|> do
    k <- cspSymbKind
    fmap (CspSymbItems k) cspSymbs

-- | parse a comma separated list of symbols
cspSymbMaps :: AParser st [CspSymbMap]
cspSymbMaps =
    do s <- cspSymbMap
       do
         _ <- commaT `followedWith` parseCspId
         is <- cspSymbMaps
         return $ s : is
        <|> return [s]

-- | parse a possible kinded list of CspCASL symbol mappings
cspSymbMapItems :: AParser st CspSymbMapItems
cspSymbMapItems = fmap (CspSymbMapItems $ CaslKind Implicit) cspSymbMaps
  <|> do
    k <- cspSymbKind
    fmap (CspSymbMapItems k) cspSymbMaps

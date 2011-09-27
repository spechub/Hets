{- |
Module      :  $Header$
Description :  Analysis and parsing of metarelations between texts
Copyright   :  (c) Eugen Kuksa, Universität Bremen 2011
License     :  GPLv2 or higher

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Analysis and parsing of metarelations between texts
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Analysis_Metarelations (metarelations) where

import CommonLogic.AS_CommonLogic
import CommonLogic.Lexer_CLIF
import CommonLogic.Lexer_Metarelations

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Data.Set (Set)
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec as Parsec

metarelations :: TEXT_MRS -> Set METARELATION
metarelations (t,mrs) = Set.union (mrels_txt t) mrs

mrels_txt :: TEXT -> Set METARELATION
mrels_txt (Text phrs _) = Set.unions $ map mrels_phr phrs
mrels_txt (Named_text _ t _) = mrels_txt t

mrels_phr :: PHRASE -> Set METARELATION
mrels_phr (Comment_text (Comment c _) _ _) = mrels c
mrels_phr _ = Set.empty

mrels :: String -> Set METARELATION
mrels s = case runParser parse_mrels (AnnoState.emptyAnnos ()) "" s of
  Right mr -> Set.singleton mr
  Left err -> Set.empty

parse_mrels :: CharParser st METARELATION
parse_mrels = parens $ do
    relativeInterpretsKey
    t1 <- identifier
    delta <- identifier
    t2 <- identifier
    return $ RelativeInterprets t1 delta t2
  <|> do
    nonconservativeExtensionKey
    t1 <- identifier
    t2 <- identifier
    return $ NonconservativeExtends t1 t2

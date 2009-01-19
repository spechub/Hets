{- |
Module      :  $Header$
Description :  S-Expressions as intermediate output format
Copyright   :  (c) E. Schulz, D. Dietrich, C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

S-Expressions for the translation from HasCASL, CASL and VSE to OMDoc
-}

module Common.SExpr
  ( SExpr(..)
  , prettySExpr
  , idToSSymbol
  , transToken
  , transString
  ) where

import Common.Doc
import Common.Id
import Common.LibName
import Common.ProofUtils
import qualified Data.Map as Map
import Data.Char

data SExpr = SSymbol String | SList [SExpr] deriving (Eq, Ord, Show)

prettySExpr :: SExpr -> Doc
prettySExpr sexpr = case sexpr of
  SSymbol s -> text s
  SList l -> parens . fsep $ map prettySExpr l

-- | transform an overloaded identifier
idToSSymbol :: Int -> Id -> SExpr
idToSSymbol n i = SSymbol
  $ transQualId i . (if n < 2 then id else showString "_O" . shows n) $ ""

transQualId :: Id -> ShowS
transQualId j@(Id _ cs _) = transId $ case cs of
  i : _ | isQualName j -> i
  _ -> j

transId :: Id -> ShowS
transId (Id ts cs _) =
    showSepList id (showString . transToken) ts .
    if null cs then id else
    showString "{" . showSepList (showString "-") transId cs
    . showString "}"

transToken :: Token -> String
transToken t = if isPlace t then "_2" else transString $ tokStr t

transStringAux :: String -> String
transStringAux = concatMap (\ c -> Map.findWithDefault [c] c cMap)

transString :: String -> String
transString s = case s of
  c : r | isDigit c -> "_D" ++ c : transStringAux r
  _ -> transStringAux s

cMap :: Map.Map Char String
cMap = Map.map ('_' :) $ Map.insert '_' "1" charMap

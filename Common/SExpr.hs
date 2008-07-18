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

module Common.SExpr where

import Common.Doc
import Common.Id
import Common.ProofUtils
import qualified Data.Map as Map

data SExpr = SSymbol String | SList [SExpr] deriving (Eq, Ord, Show)

prettySExpr :: SExpr -> Doc
prettySExpr sexpr = case sexpr of
  SSymbol s -> text s
  SList l -> parens . fsep $ map prettySExpr l

-- | transform an overloaded identifier
idToSSymbol :: Int -> Id -> SExpr
idToSSymbol n i = SSymbol
  $ transId i . (if n < 2 then id else showString "_O" . shows n) $ ""

transId :: Id -> ShowS
transId (Id ts cs _) =
    showSepList id (showString . transToken) ts .
    if null cs then id else
    showString "{" . showSepList (showString "-") transId cs
    . showString "}"

transToken :: Token -> String
transToken t = if isPlace t then "_2" else transString $ tokStr t

transString :: String -> String
transString = concatMap (\ c -> Map.findWithDefault [c] c cMap)

cMap :: Map.Map Char String
cMap = Map.map ('_' :) $ Map.insert '_' "1" charMap

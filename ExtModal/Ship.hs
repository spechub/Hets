{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

monitor syntax
-}

module ExtModal.Ship where

import OWL2.ShipSyntax
import OWL2.AS

import Common.Doc
import Common.DocUtils
import Common.Parsec

import Control.Monad

import Text.ParserCombinators.Parsec

data PreOp = X | F | G | QuantF QuantifierType [ABox]
  deriving (Show, Eq, Ord)

data BinOp = Until | Impl deriving (Show, Eq, Ord)

data Foltl
  = ABoxass Bool ABox
  | Call String [String]
  | JoinedF JunctionType [Foltl]
  | PreOp PreOp Foltl
  | BinOp Foltl BinOp Foltl
  deriving (Show, Eq, Ord)

data Monitor = Monitor String [String] (Maybe String) Foltl
  deriving (Show, Eq, Ord)

ppJFoltl :: Bool -> JunctionType -> Foltl -> Doc
ppJFoltl notLast j f = case f of
    BinOp {} -> parens
    PreOp (QuantF {}) _ | notLast -> parens
    JoinedF t _ | t /= j && t == UnionOf -> parens
    _ -> id
  $ ppFoltl f

ppBFoltl :: Foltl -> Doc
ppBFoltl f = case f of
    BinOp {} -> parens
    JoinedF {} -> parens
    _ -> id
  $ ppFoltl f

ppFoltl :: Foltl -> Doc
ppFoltl ft = case ft of
  ABoxass b a -> (if b then id else (notDoc <+>)) $ ppABox a
  Call s ps -> text s <> if null ps then empty else
                        parens (sepByCommas $ map text ps)
  JoinedF t l -> case reverse l of
    [] -> empty
    f : r -> fsep . prepPunctuate (text $ case t of
      UnionOf -> "or "
      IntersectionOf -> "and ")
      . reverse $ ppJFoltl False t f : map (ppJFoltl True t) r
  PreOp p f -> let
    d1 = ppPreOp p
    d2 = ppBFoltl f
    in case p of
    QuantF {} -> fsep [d1, bullet <+> d2]
    _ -> d1 <+> d2
  BinOp f1 o f2 -> fsep
    [ ppBFoltl f1
    , text $ case o of
              Until -> "U"
              Impl -> "=>"
    , ppBFoltl f2 ]

ppPreOp :: PreOp -> Doc
ppPreOp o = case o of
  QuantF q as -> text (showQuant q) <+> sepByCommas (map ppABox as)
  _ -> text (show o)

ppMonitor :: Monitor -> Doc
ppMonitor (Monitor name ps mc ft) = fsep
  $ (text "monitor" <+> text name <>
       (if null ps then empty else parens $ sepByCommas (map text ps))
    <+> equals)
  : case mc of
      Nothing -> []
      Just c -> [doubleQuotes . text $ filter (/= '"') c]
  ++ [ppFoltl ft]

foltl, primFoltl, preFoltl, quantFoltl, andFoltl, orFoltl :: CharParser st Foltl

primFoltl = fmap (ABoxass True) (try abox)
  <|> fmap (ABoxass False) (skipKey "not" >> abox)
  <|> parent foltl

preFoltl = liftM2 PreOp
   (choice $ map (\ p -> skipKey (show p) >> return p) [X, F, G])
   preFoltl
   <|> primFoltl

quantFoltl = do
    q <- quant
    as <- sepBy abox commaP
    bulletP
    f <- foltl
    return $ PreOp (QuantF q as) f
  <|> preFoltl
  <|> do
    n <- reserved (map show [X, F, G] ++ ["monitor", "and", "or", "U"]) nominal
    ps <- optionL $ parent $ sepBy nominal commaP
    return $ Call n ps

andFoltl = binP (JoinedF IntersectionOf) "and" quantFoltl
orFoltl = binP (JoinedF UnionOf) "or" andFoltl

foltl = do
  f <- orFoltl
  option f $ liftM2 (BinOp f)
    ((skipKey "U" >> return Until) <|> (tryString "=>" >> skip >> return Impl))
    orFoltl

monitor :: CharParser st Monitor
monitor = do
  skipKey "monitor"
  n <- nominal
  ps <- optionL $ parent $ sepBy nominal commaP
  equalP
  mc <- optionMaybe $ char '"' >> many (noneOf "\n\"") << char '"'
  f <- foltl
  return $ Monitor n ps mc f

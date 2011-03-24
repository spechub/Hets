{- |
Module      :  $Header$
Description :  parsing symbol items
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

HasCASL parsable symbol items for structured specs
-}

module HasCASL.SymbItem where

import Common.Id
import Common.Token (colonST)
import Common.Keywords
import Common.Lexer
import Common.AnnoState
import Text.ParserCombinators.Parsec

import HasCASL.ParseTerm
import HasCASL.As

-- * parsers for symbols

-- | parse a (typed) symbol
symb :: AParser st Symb
symb = do
    p@(PolyId i tys _) <- parsePolyId
    do  c <- colonST
        sc <- typeScheme p
        return $ Symb i (Just $ SymbType sc) $ tokPos c
      <|> if null tys then return $ Symb i Nothing $ posOfId i else
          fail ("bound type variables for '" ++ showId i "' without type")

-- | parse a mapped symbol
symbMap :: AParser st SymbOrMap
symbMap = do
    s <- symb
    do  f <- asKey mapsTo
        optional symbKind
        t <- symb
        return $ SymbOrMap s (Just t) $ tokPos f
      <|> return (SymbOrMap s Nothing nullRange)

-- | parse kind of symbols
symbKind :: AParser st (SymbKind, Token)
symbKind = choice (map ( \ k -> do
   q <- pluralKeyword $ drop 3 $ show k
   return (k, q)) [SyKop, SyKfun, SyKpred, SyKtype, SyKsort])
  <|> do
    q <- asKey (classS ++ "es") <|> asKey classS
    return (SyKclass, q)
  <?> "kind"

-- | parse symbol items
symbItems :: AParser st SymbItems
symbItems = do
    s <- symb
    return $ SymbItems Implicit [s] [] nullRange
  <|> do
    (k, p) <- symbKind
    (is, ps) <- symbs
    return $ SymbItems k is [] $ catRange $ p : ps

symbs :: AParser st ([Symb], [Token])
symbs = do
    s <- symb
    do  c <- anComma `followedWith` symb
        (is, ps) <- symbs
        return (s : is, c : ps)
      <|> return ([s], [])

-- | parse symbol mappings
symbMapItems :: AParser st SymbMapItems
symbMapItems = do
    s <- symbMap
    return $ SymbMapItems Implicit [s] [] nullRange
  <|> do
    (k, p) <- symbKind
    (is, ps) <- symbMaps
    return $ SymbMapItems k is [] $ catRange $ p : ps

symbMaps :: AParser st ([SymbOrMap], [Token])
symbMaps = do
    s <- symbMap
    do  c <- anComma `followedWith` symb
        (is, ps) <- symbMaps
        return (s : is, c : ps)
      <|> return ([s], [])

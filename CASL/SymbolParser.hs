{- |
Module      :  $Header$
Description :  Parser for symbols in translations and reductions
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsing symbols for translations and reductions
-}

module CASL.SymbolParser
  ( symbItems
  , symbMapItems
  , opOrPredType
  , symbKind
  ) where

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.ToDoc ()

import Common.AnnoState
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token

import Text.ParserCombinators.Parsec

-- | parsing a possibly qualified identifier
symb :: [String] -> SYMB_KIND -> AParser st SYMB
symb ks k = parseId ks >>= \ i -> case k of
    Sorts_kind -> return $ Symb_id i
    _ -> case k of
        Ops_kind -> do
             c <- colonST
             o <- opType ks
             return $ Qual_id i (O_type o) $ tokPos c
        Preds_kind -> do
             c <- colonT
             p <- predType ks
             return $ Qual_id i (P_type p) $ tokPos c
        _ -> do
             c <- colonST
             t <- opOrPredType ks
             return (Qual_id i t $ tokPos c)
     <|> return (Symb_id i)

-- | parsing a type for an operation or a predicate
opOrPredType :: [String] -> AParser st TYPE
opOrPredType ks =
    do (b, s, p) <- opSort ks
       if b then return (O_type (Op_type Partial [] s p))
         else do
           c <- crossT
           (ts, ps) <- sortId ks `separatedBy` crossT
           fmap O_type (opFunSort ks (s : ts) (c : ps))
              <|> return (P_type $ Pred_type (s : ts) $ catRange $ c : ps)
         <|> fmap O_type (opFunSort ks [s] [])
         <|> return (A_type s)
    <|> fmap P_type predUnitType

-- | parsing one symbol or a mapping of one to second symbol
symbMap :: [String] -> SYMB_KIND -> AParser st SYMB_OR_MAP
symbMap ks k =
    do s <- symb ks k
       do
         f <- asKey mapsTo
         k2 <- option Implicit $ fmap fst symbKind
         case joinSymbKinds k k2 of
           Nothing -> fail $ "contradicting symbol kinds '"
             ++ showDoc k "' and '" ++ showDoc k2 "'"
           Just k3 -> do
             t <- symb ks k3
             return (Symb_map s t $ tokPos f)
        <|> return (Symb s)

joinSymbKinds :: SYMB_KIND -> SYMB_KIND -> Maybe SYMB_KIND
joinSymbKinds k1 k2 = case k1 of
  Implicit -> Just k2
  _ -> if k2 == Implicit || k1 == k2 then Just k1 else Nothing

-- | parse a kind keyword
symbKind :: AParser st (SYMB_KIND, Token)
symbKind =
  choice (map (\ (v, s) -> do
    q <- pluralKeyword s
    return (v, q))
  [(Sorts_kind, sortS), (Ops_kind, opS), (Preds_kind, predS)])
  <?> "kind"

{- | Parse a possible kinded list of comma separated CASL symbols.
     The argument is a list of keywords to avoid as identifiers. -}
symbItems :: [String] -> AParser st SYMB_ITEMS
symbItems ks =
    do (is, ps) <- symbs ks Implicit
       return (Symb_items Implicit is $ catRange ps)
    <|>
    do (k, p) <- symbKind
       (is, ps) <- symbs ks k
       return (Symb_items k is $ catRange $ p : ps)

-- | parse a comma separated list of symbols
symbs :: [String] -> SYMB_KIND -> AParser st ([SYMB], [Token])
symbs ks k =
    do s <- symb ks k
       do
         c <- commaT `followedWith` parseId ks
         (is, ps) <- symbs ks k
         return (s : is, c : ps)
        <|> return ([s], [])

-- | parse a possible kinded list of CASL symbol mappings
symbMapItems :: [String] -> AParser st SYMB_MAP_ITEMS
symbMapItems ks =
    do (is, ps) <- symbMaps ks Implicit
       return (Symb_map_items Implicit is $ catRange ps)
    <|>
    do (k, p) <- symbKind
       (is, ps) <- symbMaps ks k
       return (Symb_map_items k is $ catRange $ p : ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: [String] -> SYMB_KIND -> AParser st ([SYMB_OR_MAP], [Token])
symbMaps ks k =
    do s <- symbMap ks k
       do
         c <- commaT `followedWith` parseId ks
         (is, ps) <- symbMaps ks k
         return (s : is, c : ps)
        <|> return ([s], [])

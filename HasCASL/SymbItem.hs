{- |
Module      :  $Header$
Description :  parsing symbol items
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

HasCASL parsable symbol items for structured specs
-}

module HasCASL.SymbItem where

import Common.Id
import Common.Keywords
import Common.Lexer
import Common.AnnoState
import Text.ParserCombinators.Parsec

import HasCASL.HToken
import HasCASL.ParseTerm
import HasCASL.As
import HasCASL.AsUtils

-- * parsers for symbols
-- | parse a (typed) symbol
symb :: AParser st Symb
symb = do i <- opId
          do c <- colT
             t <- typeScheme
             return (Symb i (Just $ SymbType t) $ tokPos c)
            <|>
            do c <- qColonT
               t <- parseType
               let p = tokPos c
               return (Symb i (Just $ SymbType $ simpleTypeScheme $
                                  mkLazyType t) p)
             <|> return (Symb i Nothing $ posOfId i)

-- | parse a mapped symbol
symbMap :: AParser st SymbOrMap
symbMap =   do s <- symb
               do   f <- asKey mapsTo
                    t <- symb
                    return (SymbOrMap s (Just t) $ tokPos f)
                  <|> return (SymbOrMap s Nothing nullRange)

-- | parse kind of symbols
symbKind :: AParser st (SymbKind, Token)
symbKind = try(
        do q <- pluralKeyword opS
           return (SK_op, q)
        <|>
        do q <- pluralKeyword functS
           return (SK_fun, q)
        <|>
        do q <- pluralKeyword predS
           return (SK_pred, q)
        <|>
        do q <- pluralKeyword typeS
           return (SK_type, q)
        <|>
        do q <- pluralKeyword sortS
           return (SK_sort, q)
        <|>
        do q <- asKey (classS ++ "es") <|> asKey classS
           return (SK_class, q))
        <?> "kind"

-- | parse symbol items
symbItems :: AParser st SymbItems
symbItems = do s <- symb
               return (SymbItems Implicit [s] [] nullRange)
            <|>
            do (k, p) <- symbKind
               (is, ps) <- symbs
               return (SymbItems k is [] $ catPos $ p:ps)

symbs :: AParser st ([Symb], [Token])
symbs = do s <- symb
           do   c <- anComma `followedWith` symb
                (is, ps) <- symbs
                return (s:is, c:ps)
             <|> return ([s], [])

-- | parse symbol mappings
symbMapItems :: AParser st SymbMapItems
symbMapItems =
            do s <- symbMap
               return (SymbMapItems Implicit [s] [] nullRange)
            <|>
            do (k, p) <- symbKind
               (is, ps) <- symbMaps
               return (SymbMapItems k is [] $ catPos $ p:ps)

symbMaps :: AParser st ([SymbOrMap], [Token])
symbMaps =
        do s <- symbMap
           do   c <- anComma `followedWith` symb
                (is, ps) <- symbMaps
                return (s:is, c:ps)
             <|> return ([s], [])



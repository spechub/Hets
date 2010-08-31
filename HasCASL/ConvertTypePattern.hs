{- |
Module      :  $Header$
Description :  convert type patterns to type identifier applications
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

convert type patterns to type identifier applications
-}

module HasCASL.ConvertTypePattern
    ( toTypePattern
    , convertTypePatterns
    , convertTypePattern
    ) where

import Common.Lexer
import Common.Id
import Common.Result

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs ()

-- | store identifier application as a type pattern
toTypePattern :: (Id, [TypeArg]) -> TypePattern
toTypePattern (i, tArgs) = TypePattern i tArgs nullRange

-- | convert type patterns
convertTypePatterns :: [TypePattern] -> Result [(Id, [TypeArg])]
convertTypePatterns ts = case ts of
    [] -> return []
    s : r -> let
        Result d m = convertTypePattern s
        Result ds (Just l) = convertTypePatterns r
        in Result (d ++ ds) $ Just $ case m of
                  Nothing -> l
                  Just i -> i : l

illegalTypePattern :: TypePattern -> Result a
illegalTypePattern = mkError "illegal type pattern"

illegalTypePatternArg :: TypePattern -> Result a
illegalTypePatternArg = mkError "illegal type pattern argument"

illegalTypeId :: TypePattern -> Result a
illegalTypeId = mkError "illegal type pattern identifier"

-- | convert a type pattern
convertTypePattern :: TypePattern -> Result (Id, [TypeArg])
convertTypePattern tp = case tp of
    TypePattern t as _ -> return (t, as)
    TypePatternToken t ->
      if isPlace t then illegalTypePattern tp else return (simpleIdToId t, [])
    MixfixTypePattern [ra, ri@(TypePatternToken inTok), rb] ->
      if head (tokStr inTok) `elem` signChars
      then let inId = Id [Token place $ getRange ra, inTok,
                           Token place $ getRange rb] [] nullRange
            in case (ra, rb) of
            (TypePatternToken (Token "__" _),
             TypePatternToken (Token "__" _)) -> return (inId, [])
            _ -> do a <- convertToTypeArg ra
                    b <- convertToTypeArg rb
                    return (inId, [a, b])
      else case ra of
         TypePatternToken t1 -> do
             a <- convertToTypeArg ri
             b <- convertToTypeArg rb
             return (simpleIdToId t1, [a, b])
         _ -> illegalTypePattern tp
    MixfixTypePattern (TypePatternToken t1 : rp) ->
      if isPlace t1 then case rp of
               [TypePatternToken inId, TypePatternToken t2] ->
                   if isPlace t2 && head (tokStr inId) `elem` signChars
                     then return (Id [t1,inId,t2] [] nullRange, [])
                   else illegalTypePattern tp
               _ -> illegalTypePattern tp
      else case rp of
         BracketTypePattern Squares as@(_:_) ps : rp2 -> do
             is <- mapM convertToId as
             rs <- mapM convertToTypeArg rp2
             return (Id [t1] is ps, rs)
         _ -> do
           as <- mapM convertToTypeArg rp
           return (simpleIdToId t1, as)
    BracketTypePattern bk [ap] ps -> case bk of
      Parens -> convertTypePattern ap
      _ -> let (o, c) = getBrackets bk
               tid = Id [Token o ps, Token place $ getRange ap,
                         Token c ps] [] nullRange
           in case ap of
         TypePatternToken t -> if isPlace t then
             return (tid, [])
             else return (tid, [TypeArg (simpleIdToId t) NonVar MissingKind
                                        rStar 0 Other nullRange])
         _ -> do a <- convertToTypeArg ap
                 return (tid, [a])
    _ -> illegalTypePattern tp

convertToTypeArg :: TypePattern -> Result TypeArg
convertToTypeArg tp = case tp of
    TypePatternToken t -> if isPlace t then illegalTypePatternArg tp else
        return $ TypeArg (simpleIdToId t)
               NonVar MissingKind rStar 0 Other nullRange
    TypePatternArg a _ ->  return a
    BracketTypePattern Parens [stp] _ ->  convertToTypeArg stp
    _ -> illegalTypePatternArg tp

convertToId :: TypePattern -> Result Id
convertToId tp = case tp of
    TypePatternToken t ->
        if isPlace t then illegalTypeId tp else return $ Id [t] [] nullRange
    MixfixTypePattern [] -> error "convertToId: MixfixTypePattern []"
    MixfixTypePattern (hd : tps) ->
         if null tps then convertToId hd
         else do
         let (toks, comps) = break ( \ p ->
                        case p of BracketTypePattern Squares (_:_) _ -> True
                                  _ -> False) tps
         ts <- mapM convertToToks (hd:toks)
         (is, ps) <- if null comps then return ([], nullRange)
                     else convertToIds $ head comps
         pls <- if null comps then return []
                else mapM convertToPlace $ tail comps
         return $ Id (concat ts ++ pls) is ps
    _ -> do
        ts <- convertToToks tp
        return $ Id ts [] nullRange

convertToIds :: TypePattern -> Result ([Id], Range)
convertToIds tp = case tp of
    BracketTypePattern Squares tps@(_ : _) ps -> do
        is <- mapM convertToId tps
        return (is, ps)
    _ -> illegalTypeId tp

convertToToks :: TypePattern -> Result [Token]
convertToToks tp = case tp of
    TypePatternToken t -> return [t]
    BracketTypePattern bk [stp] ps -> case bk of
        Parens -> illegalTypeId stp
        _ -> let [o,c] = mkBracketToken bk ps in do
            ts <- convertToToks tp
            return (o : ts ++ [c])
    MixfixTypePattern tps -> do
        ts <- mapM convertToToks tps
        return $ concat ts
    _ -> illegalTypeId tp

convertToPlace :: TypePattern -> Result Token
convertToPlace tp = case tp of
    TypePatternToken t -> if isPlace t then return t else illegalTypeId tp
    _ -> illegalTypeId tp

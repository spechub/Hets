{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2004 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable
    
   converting literals 
-}

module Common.ConvertLiteral where

import Common.Id
import Common.Lexer
import Common.GlobalAnnotations
import Common.Result

type AsAppl a = Id -> [a] -> [Pos] -> a

inc :: Int -> Pos -> Pos
inc n p = incSourceColumn p n

makeStringTerm :: Id -> Id -> AsAppl a -> Token -> a
makeStringTerm c f asAppl tok = 
  makeStrTerm (map (inc 1) sp) str
  where 
  sp = tokPos tok
  str = init (tail (tokStr tok))
  makeStrTerm p l = 
    if null l then asAppl c [] p
    else let (hd, tl) = splitString caslChar l
         in asAppl f [asAppl (Id [Token ("'" ++ hd ++ "'") p] [] []) [] p, 
                      makeStrTerm (map (inc $ length hd) p) tl] p

makeNumberTerm :: Id -> AsAppl a -> Token -> a
makeNumberTerm f asAppl t@(Token n p) =
    case n of
           [] -> error "makeNumberTerm"
           [_] -> asAppl (Id [t] [] []) [] p
           hd:tl -> asAppl f [asAppl (Id [Token [hd] p] [] []) [] p, 
                              makeNumberTerm f asAppl (Token tl 
                                                $ map (inc 1) p)] p

makeFraction :: Id -> Id -> AsAppl a -> Token -> a
makeFraction f d asAppl t@(Token s p) = 
    let (n, r) = span (\c -> c /= '.') s
        dotOffset = length n 
    in if null r then makeNumberTerm f asAppl t
       else asAppl d [makeNumberTerm f asAppl (Token n p),
                      makeNumberTerm f asAppl $ Token (tail r) 
                                      $ map (inc $ dotOffset + 1) p]
            $ map (inc dotOffset) p 

makeSignedNumber :: Id -> AsAppl a -> Token -> a
makeSignedNumber f asAppl t@(Token n p) = 
  case n of 
  [] -> error "makeSignedNumber"
  hd:tl ->   
    if hd == '-' || hd == '+' then
       asAppl (Id [Token [hd] p] [] []) 
                  [makeNumberTerm f asAppl $ Token tl 
                                         $ map (inc 1) p] p
    else makeNumberTerm f asAppl t

makeFloatTerm :: Id -> Id -> Id -> AsAppl a -> Token -> a
makeFloatTerm f d e asAppl t@(Token s p) = 
    let (m, r) = span (\c -> c /= 'E') s
        offset = length m
    in if null r then makeFraction f d asAppl t
       else asAppl e [makeFraction f d asAppl (Token m p),
                      makeSignedNumber f asAppl $ Token (tail r)
                                          $ map (inc $ offset + 1) p]
                $ map (inc offset) p

-- analyse Mixfix_token
convertMixfixToken ::  LiteralAnnos -> AsAppl a 
                  -> (Token -> a) -> Token -> ([Diagnosis], a) 
convertMixfixToken ga asAppl toTerm t = 
     if isString t then 
        case string_lit ga of
        Nothing -> err "string"
        Just (c, f) -> ([], makeStringTerm c f asAppl t)
     else if isNumber t then
          case number_lit ga of
          Nothing -> err "number"
          Just f -> if isFloating t then
                        case float_lit ga of
                        Nothing -> err "floating"
                        Just (d, e) -> ([], makeFloatTerm f d e asAppl t)
                    else ([], makeNumberTerm f asAppl t)
     else ([], te)
    where te =  toTerm t
          err s = ([Diag Error ("missing %" ++ s ++ " annotation") (tokPos t)]
                  , te)

{- |
Module      :  $Header$
Description :  generic conversion of literals
Copyright   :  Christian Maeder and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Generically converting literals
-}

module Common.ConvertLiteral
    ( SplitM
    , isGenLiteral
    , isGenNumber
    , isGenNum
    , isGenString
    , isGenList
    , isGenFloat
    , isGenFrac
    , toNumber
    , toFrac
    , toFloat
    , toString
    , toMixfixList
    ) where

import Common.Id
import Common.GlobalAnnotations
import Data.Char (isDigit)
import Data.List (isPrefixOf)

-- * test if term is a literal

type SplitM a = a -> Maybe (Id, [a])

isGenLiteral :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenLiteral splt ga i trm =
       or [ isGenNumber splt ga i trm
          , isGenString splt ga i trm
          , isGenList   splt ga i trm
          , isGenFloat  splt ga i trm
          , isGenFrac   splt ga i trm
          ]

-- | is a number or a single digit
isGenNum :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenNum splt ga i trs = case trs of
    [] -> digitTest i
    _ -> isGenNumber splt ga i trs

-- | is a number of more than one digit
isGenNumber :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenNumber splt ga i trs = case trs of
    [_, _] -> getLiteralType ga i == Number
              && all (sameId splt digitTest i) trs
    _ -> False

digitTest :: Id -> Bool
digitTest ii = case ii of
                         Id [t] [] _ -> case tokStr t of
                             [d] -> isDigit d
                             _ -> False
                         _ -> False

isGenSignedNumber :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenSignedNumber splt ga i trs =
    case trs of
    [hd] -> case splt hd of
            Just (ni, nt) -> isSign i && isGenNum splt ga ni nt
            Nothing -> False
    _ -> False

isSign :: Id -> Bool
isSign i = case i of
           Id [tok, p] [] _ | isPlace p ->
              let ts = tokStr tok in ts == "-" || ts == "+"
           _ -> False

isGenString :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenString splt ga i trs = case getLiteralType ga i of
                    StringNull -> null trs
                    StringCons _ -> all (sameId splt stringTest i) trs
                    _ -> False
    where
          stringTest ii = case getLiteralType ga ii of
                          StringNull -> True
                          _ -> case ii of
                               Id [t] [] _ -> isPrefixOf "'" $ tokStr t
                               _           -> False

isGenList :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenList splt ga i trms =
                   (case getLiteralType ga i of
                     ListNull _ -> null trms
                     ListCons _ n -> listTest n i trms
                     _ -> False)
    where listTest n1 i1 terms = case getLiteralType ga i1 of
              ListNull _ -> n1 == i1 && null terms
              ListCons _ n2 -> n1 == n2 && case terms of
                               [_, hd] -> case splt hd of
                                    Just (i2, ts) -> listTest n1 i2 ts
                                    Nothing -> False
                               _ -> False
              _ -> False

isGenFloat :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenFloat splt ga i [l, r] =
    case getLiteralType ga i of
    Floating -> case (splt l, splt r) of
        (Just (li, ltrm), Just (ri, rtrm)) ->
            (isGenNum splt ga li ltrm || isGenFrac splt ga li ltrm) &&
            (isGenSignedNumber splt ga ri rtrm || isGenNum splt ga ri rtrm)
        _ -> False
    _ -> False
isGenFloat _ _ _ _ = False

isGenFrac :: SplitM a -> GlobalAnnos -> Id -> [a] -> Bool
isGenFrac splt ga i [l, r] =
    case getLiteralType ga i of
    Fraction -> case (splt l, splt r) of
       (Just (li, ltrm), Just (ri, rtrm)) ->
                   isGenNum splt ga li ltrm && isGenNum splt ga ri rtrm
       _ -> False
    _ -> False
isGenFrac _ _ _ _ = False

sameId :: SplitM a -> (Id -> Bool) -> Id -> a -> Bool
sameId splt test i t = case splt t of
    Just (j, ts) -> if null ts then test j
                    else j == i && all (sameId splt test i) ts
    _ -> False

-- * convert an application back to a literal

joinToken :: Token -> Token -> Token
joinToken (Token s1 _) (Token s2 _) =
    Token (s1 ++ s2) nullRange -- forget the range

toSignedNumber :: (a -> (Id, [a])) -> Id -> [a] -> Token
toSignedNumber splt (Id [sign, p] [] _) [hd] | isPlace p = case splt hd of
  (i, ts) -> joinToken sign $ toNumber splt i ts
toSignedNumber _ _ _ = error "toSignedNumber"

toNumber :: (a -> (Id, [a])) -> Id -> [a] -> Token
toNumber splt i ts = if null ts then case i of
    Id [d] [] _ -> d
    _ -> error "toNumber"
    else foldr1 joinToken $ map (toNumber2 splt) ts

toNumber2 :: (a -> (Id, [a])) -> a -> Token
toNumber2 splt t = case splt t of (j, args) -> toNumber splt j args

toFrac :: (a -> (Id, [a])) -> [a] -> Token
toFrac splt [lt, rt] =
    joinToken (toNumber2 splt lt) $
              joinToken (Token "." nullRange) $
                      toNumber2 splt rt
toFrac _ _ = error "toFrac"

toFloat :: (a -> (Id, [a])) -> GlobalAnnos -> [a] -> Token
toFloat splt ga [lt, rt] =
    case (splt lt, splt rt) of
    ((bas_i, bas_t), (ex_i, ex_t)) ->
        let t1 = if isGenFrac (Just . splt) ga bas_i bas_t then
                 toFrac splt bas_t else
                 toNumber splt bas_i bas_t
            t2 = if isGenSignedNumber (Just . splt) ga ex_i ex_t then
                 toSignedNumber splt ex_i ex_t else
                 toNumber splt ex_i ex_t
        in joinToken t1 $ joinToken (Token "E" nullRange) t2
toFloat _ _ _ = error "toFloat2"

toChar :: Token -> String
toChar t = case tokStr t of
           '\'' : rt -> init rt
           _ -> error "toChar"

toString :: (a -> (Id, [a])) -> GlobalAnnos -> Id -> [a] -> Token
toString splt ga i ts =
  Token ( "\"" ++ toString1 splt ga i ts ++ "\"") nullRange

-- | the string without double quotes
toString1 :: (a -> (Id, [a])) -> GlobalAnnos -> Id -> [a] -> String
toString1 splt ga i ts = if null ts then
    case getLiteralType ga i of
    StringNull -> ""
    _ -> case i of
         Id [c] [] _ -> toChar c
         _ -> error "toString"
    else concatMap (toString2 splt ga) ts

toString2 :: (a -> (Id, [a])) -> GlobalAnnos -> a -> String
toString2 splt ga t = case splt t of (i, ts) -> toString1 splt ga i ts

-- | get list elements
getListElems :: (a -> (Id, [a])) -> [a] -> [a]
getListElems splt ts = case ts of
                     [] -> []
                     [ft, rt] -> ft : getListElems splt (snd $ splt rt)
                     _ -> error "getListElems"

-- | construct list result from application
toMixfixList :: (Id -> [a] -> Id -> b) -> (a -> (Id, [a]))
             -> GlobalAnnos -> Id -> [a] -> b
toMixfixList mkList splt ga i ts =
   let args = getListElems splt ts
       (openL, closeL, comps) = getListBrackets $
                case getLiteralType ga i of
                ListNull b -> b
                ListCons b _ -> b
                _ -> error "print_Literal_text"
   in mkList (Id openL [] nullRange) args (Id closeL comps nullRange)

{- |
Module      :  $Header$
Description :  Parser for OP-ITEMs (operation declarations and definitions)
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for OP-ITEMs (operation declarations and definitions)
-}

{-
   parse OP-ITEM and "op/ops OP-ITEM ; ... ; OP-ITEM"
   parse PRED-ITEM and "op/ops PRED-ITEM ; ... ; PRED-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.OpItem (opItem, predItem) where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Text.ParserCombinators.Parsec
import Common.Token
import CASL.Formula
import Data.List(sort)

-- stupid cast
argDecl :: [String] -> AParser st ARG_DECL
argDecl = fmap (\(Var_decl vs s ps) -> Arg_decl vs s ps) . varDecl

-- non-empty
predHead :: [String] -> AParser st PRED_HEAD
predHead ks =
    do o <- wrapAnnos oParenT
       (vs, ps) <- argDecl ks `separatedBy` anSemi
       p <- addAnnos >> cParenT
       return $ Pred_head vs $ catRange (o:ps++[p])

opHead :: [String] -> AParser st OP_HEAD
opHead ks =
    do Pred_head vs ps <- predHead ks
       c <- anColon
       (b, s, qs) <- opSort ks
       return $ Op_head (if b then Partial else Total) vs s
              (ps `appRange` tokPos c `appRange` qs)

opAttr :: AParsable f => [String] -> AParser st (OP_ATTR f, Token)
opAttr ks = do p <- asKey assocS
               return (Assoc_op_attr, p)
            <|>
            do p <- asKey commS
               return (Comm_op_attr, p)
            <|>
            do p <- asKey idemS
               return (Idem_op_attr, p)
            <|>
            do p <- asKey unitS
               t <- term ks
               return (Unit_op_attr t, p)

isConstant :: OP_TYPE -> Bool
isConstant(Op_type _ [] _ _) = True
isConstant _ = False

toHead :: Range -> OP_TYPE -> OP_HEAD
toHead (Range c) (Op_type k [] s ps) = Op_head k [] s (Range c `appRange` ps)
toHead _ _ = error "toHead got non-empty argument type"

opItem :: AParsable f => [String] -> AParser st (OP_ITEM f)
opItem ks =
    do (os, cs)  <- parseId ks `separatedBy` anComma
       if isSingle os then
              do c <- anColon
                 t <- opType ks
                 if isConstant t then
                     opBody ks (head os) (toHead (tokPos c) t)
                     <|> opAttrs ks os t [c]  -- this always succeeds
                   else opAttrs ks os t [c]
              <|> (opHead ks >>= opBody ks (head os))
          else do
            c <- anColon
            t <- opType ks
            opAttrs ks os t $ cs ++ [c]

opBody :: AParsable f => [String] -> OP_NAME -> OP_HEAD
       -> AParser st (OP_ITEM f)
opBody ks o h =
    do e <- equalT
       a <- annos
       t <- term ks
       return $ Op_defn o h (Annoted t nullRange a []) $ tokPos e

opAttrs :: AParsable f => [String] -> [OP_NAME] -> OP_TYPE -> [Token]
        -> AParser st (OP_ITEM f)
opAttrs ks os t c =
    do q <- anComma
       (as, cs) <- opAttr ks `separatedBy` anComma
       let ps = Range (sort (catPosAux (c ++ map snd as ++ (q:cs))))
       return (Op_decl os t (map fst as) ps)
   <|> return (Op_decl os t [] (catRange c))

-- overlap "o:t" DEF-or DECL "o:t=e" or "o:t, assoc"

-- ----------------------------------------------------------------------
-- predicates
-- ----------------------------------------------------------------------

predItem :: AParsable f => [String] -> AParser st (PRED_ITEM f)
predItem ks =
    do (ps, cs)  <- parseId ks `separatedBy` anComma
       if isSingle ps then
                predBody ks (head ps) (Pred_head [] nullRange)
                <|> (predHead ks >>= predBody ks (head ps))
                <|> predTypeCont ks ps cs
         else predTypeCont ks ps cs

predBody :: AParsable f => [String] -> PRED_NAME -> PRED_HEAD
         -> AParser st (PRED_ITEM f)
predBody ks p h =
    do e <- asKey equivS
       a <- annos
       f <- formula ks
       return $ Pred_defn p h (Annoted f nullRange a []) $ tokPos e

predTypeCont :: [String] -> [PRED_NAME] -> [Token] -> AParser st (PRED_ITEM f)
predTypeCont ks ps cs =
    do c <- colonT
       t <- predType ks
       return $ Pred_decl ps t $ catRange (cs++[c])

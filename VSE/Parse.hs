{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for VSE logic extension of CASL
-}

module VSE.Parse where

import Common.AnnoState
import Common.DocUtils
import Common.Id
import Common.Lexer
import Common.Result
import Common.Token
import VSE.As
import Text.ParserCombinators.Parsec
import CASL.Formula
import CASL.AS_Basic_CASL
import Data.Char (toUpper, toLower)

declWords :: [String]
declWords = let
  ps = ["procedure", "function"]
  rs = ps ++ map (++ "s") ps
  in rs ++ map (map toUpper) rs

reservedWords :: [String]
reservedWords = let
  rs =
    [ "in", "out", "begin", "end", "abort", "skip", "return", "declare"
    , "if", "then", "else", "fi", "while", "do", "od"
    , "defprocs", "defprocsend" ]
  in [ "<:", ":>"] ++ declWords ++ rs ++ map (map toUpper) rs

keyword :: String -> CharParser st Token
keyword s = pToken $ try $ do
   str <- scanAnyWords
   if map toLower str == s then return s else unexpected str <?> map toUpper s

vseVarDecl :: AParser st VarDecl
vseVarDecl = do
  v <- varId reservedWords
  c <- colonT
  s <- sortId reservedWords
  option (VarDecl v s Nothing $ tokPos c) $ do
    a <- asKey ":="
    t <- term reservedWords
    return $ VarDecl v s (Just t) $ toRange c [] a

fromVarDecl :: [VarDecl] -> Program -> ([VAR_DECL], Program)
fromVarDecl vs p = case vs of
  [] -> ([], p)
  VarDecl v s mt r : n ->
      let (rs, q) = fromVarDecl n p
      in (Var_decl [v] s r : rs, case mt of
           Nothing -> q
           Just t -> Ranged (Seq (Ranged (Assign v t) r) q) r)

program :: AParser st Program
program = do
    t <- keyword "abort"
    return $ Ranged Abort $ tokPos t
  <|> do
    t <- keyword "skip"
    return $ Ranged Skip $ tokPos t
  <|> do
    r <- keyword "return"
    t <- term reservedWords
    return $ Ranged (Return t) $ tokPos r
  <|> do
    b <- keyword "begin"
    p <- programSeq
    e <- keyword "end"
    return $ Ranged (Block [] p) $ toRange b [] e
  <|> do
    d <- keyword "declare"
    (vs, ps) <- separatedBy vseVarDecl commaT
    s <- anSemi
    p <- programSeq
    let (cs, q) = fromVarDecl vs p
    return $ Ranged (Block cs q) $ toRange d ps s
  <|> do
    i <- keyword "if"
    c <- formula reservedWords
    p <- keyword "then"
    t <- programSeq
    do  r <- keyword "fi"
        let s = toRange i [p] r
        return $ Ranged (If c t $ Ranged Skip s) s
      <|> do
        q <- keyword "else"
        e <- programSeq
        r <- keyword "fi"
        return $ Ranged (If c t e) $ toRange i [p, q] r
  <|> do
    w <- keyword "while"
    c <- formula reservedWords
    d <- keyword "do"
    p <- programSeq
    o <- keyword "od"
    return $ Ranged (While c p) $ toRange w [d] o
  <|> do
    (v, a) <- try $ do
         v <- varId reservedWords
         a <- asKey ":="
         return (v, a)
    t <- term reservedWords
    return $ Ranged (Assign v t) $ tokPos a
  <|> do
    p <- parseId reservedWords
    o <- oParenT
    (ts, ps) <- option ([], []) $
       term reservedWords `separatedBy` commaT
    c <- cParenT
    return $ Ranged (Call p ts) $ toRange o ps c

programSeq :: AParser st Program
programSeq = do
  p1 <- program
  option p1 $ do
    s <- semiT
    p2 <- programSeq
    return $ Ranged (Seq p1 p2) $ tokPos s

procKind :: CharParser st (ProcKind, Token)
procKind = do
    k <- keyword "procedure"
    return (Proc, k)
  <|> do
    k <- keyword "function"
    return (Func, k)

defproc :: AParser st Defproc
defproc = do
  (pk, q) <- procKind
  i <- parseId reservedWords
  o <- oParenT
  (ts, ps) <- option ([], []) $
       varId reservedWords `separatedBy` commaT
  c <- cParenT
  p <- program
  return $ Defproc pk i ts p $ toRange q (o : ps) c

boxOrDiamandProg :: AParser st (Token, BoxOrDiamond, Program, Token)
boxOrDiamandProg = do
    o <- asKey "<:"
    p <- programSeq
    c <- asKey ":>"
    return (o, Diamond, p, c)
  <|> do
    o <- asKey "[:"
    p <- programSeq
    c <- asKey ":]"
    return (o, Box, p, c)

dlformula :: AParser st Dlformula
dlformula = do
    p <- keyword "defprocs"
    (ps, qs) <- separatedBy defproc semiT
    q <- keyword "defprocsend"
    return $ Ranged (Defprocs ps) $ toRange p qs q
  <|> do
   (o, b, p, c) <- boxOrDiamandProg
   f <- formula reservedWords
   return $ Ranged (Dlformula b p f) $ toRange o [] c

param :: CharParser st Procparam
param = do
    k <- (keyword "in" >> return In) <|> (keyword "out" >> return Out)
    s <- sortId reservedWords
    return $ Procparam k s

profile :: AParser st Profile
profile = do
  (ps, _) <- option ([], []) $ separatedBy param commaT
  m <- optionMaybe $ asKey "->" >> sortId reservedWords
  return $ Profile ps m

procdecl :: AParser st Sigentry
procdecl = do
  i <- parseId reservedWords
  c <- colonT
  p <- profile
  return $ Procedure i p $ tokPos c

procdecls :: AParser st Procdecls
procdecls = do
  k <- keyword "procedures" <|> keyword "procedure"
  auxItemList (declWords ++ startKeyword) [k] procdecl Procdecls

instance AParsable Dlformula where
  aparser = dlformula

instance AParsable Procdecls where
  aparser = procdecls

-- | just for testing
testParse :: String -> String
testParse str = case runParser (formula [] :: AParser () Sentence)
    (emptyAnnos ()) "" str of
  Left err -> showErr err
  Right ps -> showDoc ps ""

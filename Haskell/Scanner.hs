{- |
Module      :  $Header$
Description :  scan tokens of Haskell sources
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Haskell.Scanner
  ( splitLines
  , showScan
  , processScan
  , scan
  ) where

import Haskell.Wrapper

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Common.Parsec

import Control.Monad
import Data.Char
import Data.List

number :: Parser String
number =
    try (char '0' <:> single (oneOf "oO")) <++> many octDigit
  <|>
    try (char '0' <:> single (oneOf "xX")) <++> many hexDigit
  <|> many1 digit
          <++> optionL (try (char '.' <:> single digit) <++> many digit)
          <++> optionL (try (oneOf "eE" <:> optionL (single $ oneOf "+-")
                             <++> single digit) <++> many digit)

hChar :: Parser Char
hChar = alphaNum <|> oneOf "_'"

uL :: Parser Char
uL = char '_'

lId :: Parser String
lId = (uL <|> lower) <:> many hChar

uId :: Parser String
uId = upper <:> many hChar

opSym :: Parser Char
opSym = oneOf "!#$%&*+-./:<=>?@\\^|~"

op :: Parser String
op = many1 opSym

data QualElem = Var | Sym | Cons deriving Eq

data QualName = Name Bool QualElem String

instance Show QualName where
  show (Name _ _ s) = s

qId :: Parser QualName
qId = fmap (Name False Var) lId
  <|> fmap (Name False Sym) op
  <|> do
    n <- uId
    option (Name False Cons n) $ do
      d <- try (char '.' << lookAhead (uL <|> letter <|> opSym))
      Name _ k r <- qId
      return $ Name True k $ n ++ d : r

infixOp :: Parser String
infixOp = enclosedBy (fmap show qId) $ char '`'

seps :: String
seps = "[({,;})]"

data TokenKind = Comment | White | Indent | Literal | Infix

data Token
  = QualName QualName
  | Sep Char
  | Token TokenKind String

isIndent :: Token -> Bool
isIndent t = case t of
  Token Indent _ -> True
  _ -> False

isInfixOp :: Token -> Bool
isInfixOp t = case t of
  QualName (Name _ Sym s) -> notElem s $ map (: []) "~@#"
  Token Infix _ -> True
  _ -> False

isComment :: Token -> Bool
isComment t = case t of
  Token Comment _ -> True
  _ -> False

isSepIn :: String -> Token -> Bool
isSepIn cs t = case t of
  Sep c -> elem c cs
  _ -> False

isOpPar :: Token -> Bool
isOpPar = isSepIn "[({"

isClPar :: Token -> Bool
isClPar = isSepIn "})]"

isOpParOrInfix :: Token -> Bool
isOpParOrInfix t = isOpPar t || isInfixOp t

isClParOrInfix :: Token -> Bool
isClParOrInfix t = isClPar t || isInfixOp t

isNonPar :: Token -> Bool
isNonPar = isSepIn ",;"

isWhiteTok :: Token -> Bool
isWhiteTok t = case t of
  Token White _ -> True
  _ -> False

isInfixMinusOp :: Token -> Bool
isInfixMinusOp t = case t of
  QualName (Name _ k _) -> k /= Sym
  Sep _ -> isClPar t
  Token k _ -> case k of
    Literal -> True
    Infix -> True
    _ -> False

noSpaceNeededBefore :: Token -> Bool
noSpaceNeededBefore t = isSepIn ",;})]" t || isWhiteTok t || show t == "@"

noSpaceNeededAfter :: Token -> Bool
noSpaceNeededAfter t = isOpPar t || elem (show t) (map (: []) "-~@#")

instance Show Token where
  show t = case t of
    QualName q -> show q
    Sep c -> [c]
    Token _ s -> s

isWhite :: Char -> Bool
isWhite c = isSpace c && c /= '\n'

white :: Parser String
white = many $ satisfy isWhite

indent :: Parser String
indent = newline <:> white

tok :: Parser Token
tok = fmap (Token Comment) (nestComment <|> lineComment)
  <|> fmap QualName qId
  <|> fmap Sep (oneOf seps)
  <|> fmap (Token Literal) (charLit <|> stringLit <|> number)
  <|> fmap (Token Infix) infixOp
  <|> fmap (Token Indent) indent

tokPos :: Parser (SourcePos, Token)
tokPos = pair getPosition tok

whitePos :: Parser (SourcePos, Token)
whitePos = pair getPosition $ fmap (Token White) white

scan :: Parser [(SourcePos, Token)]
scan = fmap (\ (p, Token _ s) -> (p, Token Indent s)) whitePos
    <:> flat (many $ liftM2
        (\ t w@(_, Token _ s) -> if null s then [t] else [t, w])
        tokPos whitePos) << eof

splitBy :: (a -> Bool) -> [a] -> [[a]]
splitBy p l = let (fr, rt) = break p l in fr : case rt of
  [] -> []
  d : tl -> let hd : tll = splitBy p tl in (d : hd) : tll

splitLines :: [(SourcePos, Token)] -> [[(SourcePos, Token)]]
splitLines = splitBy (isIndent . snd)

anaLine :: [(SourcePos, Token)] -> [String]
anaLine l = case l of
  [] -> []
  (p, Token Comment s) : r -> let
    n = adjustComment s
    s5 = take 5 s
    nr = take 5 $ reverse n
    sr = take 5 $ reverse s
    in [ show p ++ " non-conventional comment start: " ++ s5 | s5 /= take 5 n ]
       ++ [ show (updatePosString p s) ++ " non-conventional comment end: "
            ++ reverse sr | isPrefixOf "{-" s5, sr /= nr ]
       ++ anaLine r
  [(p, x)] -> case x of
    Token White _ -> [show p ++ " trailing white space"]
    Token Indent (_ : _ : _) -> [show p ++ " empty line with spaces"]
    _ -> []
  (p, Token Indent s) : r -> let (ft, rt) = span (`elem` "\n ") s in
    [ show (updatePosString p ft)
      ++ " use only blanks for indentation"
    | not (null rt) ]
    ++ anaLine r
  (_, t1) : (p2, Token White s) : r@((p3, t3) : ts) -> let
     s1 = show t1
     s3 = show t3
     n = length s
     both = filter (`elem` "[({\\`})]") $ s1 ++ s3
     pos = case both of
             _ : _ : _ -> "between"
             _ | isOpPar t1 -> "after"
               | isClPar t3 -> "before"
             _ -> "here"
     in [ show p2 ++ " no space needed " ++ pos ++ " " ++ both
        | isOpParOrInfix t1
        , isClParOrInfix t3
        , not (isInfixOp t1 && isInfixOp t3)
        ]
     ++ [ show p2 ++ " multiple (" ++ show n ++ ") blanks"
        | n > 1
        , not (isComment t3) ]
     ++ [ show p3 ++ " break line after " ++ show s3
        | elem s3 ["of", "do"], not (null ts) ]
     ++ case ts of
          (_, t4) : _
            | s1 == "::" && s3 == "!" && not (isWhiteTok t4)
              -> anaLine ts
            | s3 == "-" && not (noSpaceNeededBefore t4) && isInfixMinusOp t1
              -> (show p3 ++ " insert space after infix -") : anaLine r
          _ -> anaLine r
  (p1, t1) : r@((p2, t2) : ts) -> let
    s1 = show t1
    s2 = show t2
    n1 = length s1
    n2 = length s2
    lt = n1 <= n2
    both = s1 ++ s2
    after = case () of
      _ | isNonPar t1 -> True
        | isOpPar t2 -> False
        | s1 == "\\" -> True
        | isInfixOp t1 -> if isInfixOp t2 then lt else True
        | isInfixOp t2 -> False
      _ -> lt
    in case ts of
    (_, t3) : _
      | s2 == "-" && not (noSpaceNeededBefore t3) && isInfixMinusOp t1
        -> (show p2 ++ " put spaces around infix -") : anaLine ts
    _ -> [ show p2 ++ " leave space "
           ++ if after then "after " ++ s1 else "before " ++ s2
         | not (noSpaceNeededAfter t1)
         , not (noSpaceNeededBefore t2)]
         ++ [ show p1 ++ " but may be template haskell splice " ++ both
            | both == "$(" ]
         ++ anaLine r

untabify :: SourcePos -> String -> String
untabify p s =
  let p2 = updatePosString p s
      bs = sourceColumn p2 - sourceColumn p
  in replicate bs ' '

blankTok :: (SourcePos, Token)
blankTok = (initialPos "", Token White " ")

processLine :: [(SourcePos, Token)] -> [(SourcePos, Token)]
processLine l = case l of
  [] -> []
  (p, Token Comment s) : r ->
      (p, Token Comment $ adjustComment s) : processLine r
  (p, Token Indent s) : r ->
      (p, Token Indent $ case s of
          '\n' : w -> '\n' : untabify (initialPos "") w
          _ -> untabify p s) : processLine r
  [(_, x)] -> case x of
    Token White _ -> []
    _ -> l
  p1@(_, t1) : (p, Token White s) : r@(p3@(_, t3) : ts) -> let
     s1 = show t1
     s3 = show t3
     in p1 :
        if isOpParOrInfix t1 && isClParOrInfix t3
               && not (isInfixOp t1 && isInfixOp t3)
        then processLine r
        else if isComment t3
             then (p, Token White $ untabify p s) : processLine r
             else blankTok : case ts of
          (_, t4) : _
            | s1 == "::" && s3 == "!" && not (isWhiteTok t4)
              -> p3 : processLine ts
            | s3 == "-" && not (noSpaceNeededBefore t4) && isInfixMinusOp t1
              -> p3 : blankTok : processLine ts
          _ -> processLine r
  p1@(_, t1) : r@(p2@(_, t2) : ts) -> p1
    : case ts of
    (_, t3) : _
      | show t2 == "-" && not (noSpaceNeededBefore t3) && isInfixMinusOp t1
        -> blankTok : p2 : blankTok : processLine ts
    _ ->
      if noSpaceNeededAfter t1 || noSpaceNeededBefore t2
      then processLine r
      else blankTok : processLine r

processScan :: [[(SourcePos, Token)]] -> String
processScan = concatMap (concatMap (show . snd) . processLine)
  . removeBlankLines 1 isBlankLine . removeFinalBlankLines

showScan :: [[(SourcePos, Token)]] -> String
showScan = intercalate "\n" . concatMap anaLine


hasLongerPrefix :: String -> String -> String -> Bool
hasLongerPrefix p n s = let ps = map (\ c -> p ++ [c]) n in
  any (`isPrefixOf` s) ps

adjustPrefix :: String -> String -> String -> String
adjustPrefix p n s =
   if hasLongerPrefix p n s then s else case stripPrefix p s of
     Nothing -> s
     Just r -> p ++ case dropWhile isWhite r of
         rt@('\n' : _) -> rt
         rt -> ' ' : rt

adjustBothEnds :: String -> String -> String -> String -> String
adjustBothEnds p q n s =
    if hasLongerPrefix p n s then s else
    concatMap (reverse . dropWhile isWhite . reverse)
    $ removeBlankLines 1 (all isSpace)
    $ splitBy (== '\n')
    $ reverse $ adjustPrefix q n $ reverse $ adjustPrefix p n s

adjustComment :: String -> String
adjustComment = adjustPrefix "--" ""
    . adjustBothEnds "{-" "}-" "!#"
    . adjustBothEnds "{-!" "}-!" ""
    . adjustBothEnds "{-#" "}-#" ""

isBlankLine :: [(SourcePos, Token)] -> Bool
isBlankLine x = case x of
  [(_, Token Indent _)] -> True
  _ -> False

removeBlankLines :: Int -> ([a] -> Bool) -> [[a]] -> [[a]]
removeBlankLines c p l = case l of
  [] -> []
  x : r ->
    if p x
    then if c > 1
         then removeBlankLines c p r
         else x : removeBlankLines (c + 1) p r
    else x : removeBlankLines 0 p r

removeFinalBlankLines :: [[(SourcePos, Token)]] -> [[(SourcePos, Token)]]
removeFinalBlankLines ll = reverse $ [(initialPos "", Token Indent "\n")]
  : dropWhile (\ l -> case l of
                [(_, Token Indent _)] -> True
                _ -> False) (reverse ll)

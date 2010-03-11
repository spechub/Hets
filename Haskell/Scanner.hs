{- |
Module      :  $Header$
Description :  scan tokens of Haskell sources
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Haskell.Scanner where

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
          <++> optionL (char '.' <:> many digit)
          <++> optionL (oneOf "eE" <:> optionL (single  $ oneOf "+-")
                        <++> many digit)

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

data QualElem = Var | Sym | Cons

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
  QualName (Name _ Sym s) -> notElem s $ map (: []) "@#"
  Token Infix _ -> True
  _ -> False

isComment :: Token -> Bool
isComment t = case t of
  Token Comment _ -> True
  _ -> False

isNameOrLit :: Token -> Bool
isNameOrLit t = case t of
  Token k _ -> case k of
    Literal -> True
    _ -> False
  Sep _ -> False
  QualName _ -> not $ isInfixOp t

isSepIn :: String -> Token -> Bool
isSepIn cs t = case t of
  Sep c -> elem c cs
  _ -> False

isOpPar :: Token -> Bool
isOpPar = isSepIn "[({"

isClPar :: Token -> Bool
isClPar = isSepIn "})]"

isNonPar :: Token -> Bool
isNonPar = isSepIn ",;"

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
    <:> (flat $ many $ liftM2
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
  (_, t1) : (p2, Token White s) : r@((p3, t3) : ts) -> let
     s1 = show t1
     s3 = show t3
     n = length s
     in [ show p2 ++ " no space needed at paren"
        | isInfixOp t1 && isClPar t3 || isOpPar t1 && isInfixOp t3 ]
     ++ [ show p2 ++ " multiple (" ++ show n ++ ") blanks"
        | n > 1 || n > 2 && s1 == "infix"
        , not (isComment t3) ]
     ++ [ show p3 ++ " break line after " ++ s3
        | elem s3 ["of", "do"], not (null ts) ]
     ++ if s1 == "::" && s3 == "!" then anaLine ts else anaLine r
  (p1, t1) : r@((p2, t2) : _) ->
      (if isNonPar t1 || isInfixOp t1 then
          [ show p1 ++ " leave space after " ++ show t1 | isNameOrLit t2 ]
      else if isNameOrLit t1 then
          [ show p2 ++ " leave space before " ++ show t2 | isInfixOp t2 ]
      else []) ++ anaLine r

processLine :: [(SourcePos, Token)] -> [(SourcePos, Token)]
processLine l = case l of
  [] -> []
  (p, Token Comment s) : r ->
      (p, Token Comment $ adjustComment s) : processLine r
  [(_, x)] -> case x of
    Token White _ -> []
    _ -> l
  p1@(_, t1) : p2@(p, Token White _) : r@(p3@(_, t3) : ts) -> let
     s1 = show t1
     s3 = show t3
     in p1 :
        if isInfixOp t1 && isClPar t3 || isOpPar t1 && isInfixOp t3
        then processLine r
        else if isComment t3
             then p2 : processLine r
             else (p, Token White " ") :
                  if s1 == "::" && s3 == "!"
                  then p3 : processLine ts
                  else processLine r
  p1@(p, t1) : r@((_, t2) : _) ->
      p1 : if (isNonPar t1 || isInfixOp t1) && isNameOrLit t2
         || isNameOrLit t1 && isInfixOp t2
      then (p, Token White " ") : processLine r
      else processLine r

processScan :: [[(SourcePos, Token)]] -> String
processScan = concatMap (concatMap (show . snd) . processLine)
  . removeBlankLines 1 isBlankLine . removeFinalBlankLines

showScan :: [[(SourcePos, Token)]] -> String
showScan = intercalate "\n" . concatMap anaLine

adjustPrefix :: String -> String -> String -> String
adjustPrefix p n s = let ps = map (\ c -> p ++ [c]) n in
   if any (flip isPrefixOf s) ps then s else case stripPrefix p s of
     Nothing -> s
     Just r -> p ++ case dropWhile isWhite r of
         rt@('\n' : _) -> rt
         rt -> ' ' : rt

adjustBothEnds :: String -> String -> String -> String -> String
adjustBothEnds p q n s = let ps = map (\ c -> p ++ [c]) n in
    if any (flip isPrefixOf s) ps || not (isPrefixOf p s) then s else
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

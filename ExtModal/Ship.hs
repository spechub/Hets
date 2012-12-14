{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

monitor syntax
-}

module ExtModal.Ship where

import OWL2.ShipSyntax
import OWL2.AS

import Common.Doc
import Common.DocUtils
import Common.Parsec

import Control.Monad

import Text.ParserCombinators.Parsec

data PreOp = X | F | G | QuantF QuantifierType [ABox]
  deriving (Show, Eq, Ord)

data BinOp = Until | Impl deriving (Show, Eq, Ord)

data Foltl
  = ABoxass Bool ABox
  | Call Bool String [String]
  | JoinedF JunctionType [Foltl]
  | PreOp PreOp Foltl
  | BinOp Foltl BinOp Foltl
  deriving (Show, Eq, Ord)

data Header = Header String [String]
  deriving (Show, Eq, Ord)

data Monitor = Monitor Header (Maybe String) Foltl
  deriving (Show, Eq, Ord)

type ABoxDeletes = [Either ABox [String]]

type ABoxs = [ABox]

data CondEffect = CondEffect ABox ABoxDeletes
  deriving (Show, Eq, Ord)

data Action = Action Header ABoxs ABoxDeletes [CondEffect]
  deriving (Show, Eq, Ord)

data Process = Process Header Proc
  deriving (Show, Eq, Ord)

data IndEffect = IndEffect String ABoxs ABoxDeletes ABoxs
  deriving (Show, Eq, Ord)

data Proc
  = While ABoxs Proc
  | Star Proc
  | IfThenElse ABoxs Proc Proc
  | Switch [(ABoxs, Proc)] (Maybe Proc)
  | Forall ABoxs Proc
  | Init Foltl
  | CallP String [String]
  | BinP Proc BinP Proc
  deriving (Show, Eq, Ord)

data BinP = Semi | Pipe | SeqPlus deriving (Show, Eq, Ord)

ppJFoltl :: Bool -> JunctionType -> Foltl -> Doc
ppJFoltl notLast j f = case f of
    BinOp {} -> parens
    PreOp (QuantF {}) _ | notLast -> parens
    JoinedF t _ | t /= j && t == UnionOf -> parens
    _ -> id
  $ ppFoltl f

ppBFoltl :: Foltl -> Doc
ppBFoltl f = case f of
    BinOp {} -> parens
    _ -> id
  $ ppFoltl f

ppFoltl :: Foltl -> Doc
ppFoltl ft = case ft of
  ABoxass b a -> (if b then id else (notDoc <+>)) $ ppABox a
  Call b s ps -> (if b then keyword "run" else empty)
    <+> text s <> if null ps then empty else
                        parens (sepByCommas $ map text ps)
  JoinedF t l -> case reverse l of
    [] -> empty
    f : r -> fsep . prepPunctuate (text $ case t of
      UnionOf -> "or "
      IntersectionOf -> "and ")
      . reverse $ ppJFoltl False t f : map (ppJFoltl True t) r
  PreOp p f -> let
    d1 = ppPreOp p
    d2 = ppFoltl f
    in case p of
    QuantF {} -> fsep [d1, bullet <+> d2]
    _ -> d1 <+> d2
  BinOp f1 o f2 -> fsep
    [ ppBFoltl f1
    , case o of
              Until -> keyword "U"
              Impl -> implies
    , ppBFoltl f2 ]

ppPreOp :: PreOp -> Doc
ppPreOp o = case o of
  QuantF q as -> keyword (showQuant q) <+> sepByCommas (map ppABox as)
  _ -> keyword (show o)

ppHeader :: Header -> Doc
ppHeader (Header name ps) = text name <>
       (if null ps then empty else parens $ sepByCommas $ map text ps)
    <+> equals

ppMonitor :: Monitor -> Doc
ppMonitor (Monitor h mc ft) = fsep
  $ (keyword "monitor" <+> ppHeader h)
  : case mc of
      Nothing -> []
      Just c -> [doubleQuotes . text $ filter (/= '"') c]
  ++ [ppFoltl ft]

ppABoxDelete :: Either ABox [String] -> Doc
ppABoxDelete e = case e of
  Left a -> ppABox a
  Right l -> keyword "delete" <+> parens (sepByCommas $ map text l)

ppABoxDeletes :: ABoxDeletes -> Doc
ppABoxDeletes = sepByCommas . map ppABoxDelete

ppABoxs :: ABoxs -> Doc
ppABoxs = sepByCommas . map ppABox

ppCondEffect :: CondEffect -> Doc
ppCondEffect (CondEffect a as) =
  fsep [keyword "if" <+> parens (ppABox a), ppABoxDeletes as]

eqKey :: String -> Doc
eqKey s = keyword s <+> equals

ppAction :: Action -> Doc
ppAction (Action h pre eff cs) = fsep
  [ keyword "action" <+> ppHeader h
  , braces $ vcat
    $ [ eqKey "pre" <+> ppABoxs pre
      , eqKey "effect" <+> ppABoxDeletes eff]
    ++ map ppCondEffect cs]

ppProcess :: Process -> Doc
ppProcess (Process h p) = fsep
  [ keyword "process" <+> ppHeader h, braces $ ppProc p]

ppIndEffect :: IndEffect -> Doc
ppIndEffect (IndEffect n is cs ds) = fsep
  [ keyword "indirect" <+> keyword "effect" <+> ppHeader (Header n [])
  , braces $ vcat
    [ eqKey "init" <+> ppABoxs is
    , eqKey "causes" <+> ppABoxDeletes cs
    , eqKey "cond" <+> ppABoxs ds]]

ppProc :: Proc -> Doc
ppProc _ = empty

foltl, primFoltl, preFoltl, quantFoltl, andFoltl, orFoltl :: CharParser st Foltl

primFoltl = fmap (ABoxass True) (try abox)
  <|> fmap (ABoxass False) (skipKey "not" >> (try abox <|> parent abox))
  <|> parent foltl

preFoltl = liftM2 PreOp
   (choice $ map (\ p -> skipKey (show p) >> return p) [X, F, G])
   foltl
   <|> primFoltl

quantFoltl = do
    q <- quant << skip
    as <- sepBy abox commaP
    bulletP
    f <- foltl
    return $ PreOp (QuantF q as) f
  <|> preFoltl
  <|> (option False (skipKey "run" >> return True) >>= callFoltl)

andFoltl = binP (JoinedF IntersectionOf) "and" quantFoltl
orFoltl = binP (JoinedF UnionOf) "or" andFoltl

foltl = do
  f <- orFoltl
  option f $ liftM2 (BinOp f)
    ((skipKey "U" >> return Until) <|> (tryString "=>" >> skip >> return Impl))
    foltl

callFoltl :: Bool -> GenParser Char st Foltl
callFoltl b = liftM2 (Call b)
    (reserved (map show [X, F, G]
                   ++ ["run", "monitor", "and", "or", "U"]) nominal)
    . optionL . parent $ sepBy nominal commaP

header :: CharParser st Header
header =
  liftM2 Header nominal (optionL $ parent $ sepBy nominal commaP) << equalP

monitor :: CharParser st Monitor
monitor = do
  skipKey "monitor"
  h <- header
  mc <- optionMaybe $ char '"' >> many (noneOf "\n\"") << skipChar '"'
  f <- foltl
  return $ Monitor h mc f

mon :: CharParser st [Monitor]
mon = many1 monitor

ppMon :: [Monitor] -> Doc
ppMon = vsep . map ppMonitor

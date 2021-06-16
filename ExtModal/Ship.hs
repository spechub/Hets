{- |
Module      :  ./ExtModal/Ship.hs
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

monitor syntax
-}

module ExtModal.Ship where

import OWL2.ShipSyntax
import qualified OWL2.AS as AS

import Common.Doc
import Common.DocUtils
import Common.Parsec

import Control.Monad

import Text.ParserCombinators.Parsec

data PreOp = NotF | X | F | G | QuantF QuantifierType [ABox]
  deriving (Show, Eq, Ord)

data BinOp = Until | Impl deriving (Show, Eq, Ord)

data Foltl
  = ABoxass ABox
  | Call Bool String [String] -- True: run a process, but deprecated
  | JoinedF JunctionType [Foltl]
  | PreOp PreOp Foltl
  | BinOp Foltl BinOp Foltl
  deriving (Show, Eq, Ord)

constFoltl :: String -> Foltl
constFoltl s = Call False s []

trueFoltl, falseFoltl :: Foltl
trueFoltl = constFoltl "true"
falseFoltl = constFoltl "false"

negFoltl :: Foltl -> Foltl
negFoltl ftl = let nftl = PreOp NotF ftl in case ftl of
  ABoxass _ -> nftl
  Call {} | trueFoltl == ftl -> falseFoltl
          | falseFoltl == ftl -> trueFoltl
          | otherwise -> nftl
  JoinedF t fs -> JoinedF (case t of
    UnionOf -> IntersectionOf
    IntersectionOf -> UnionOf) $ map negFoltl fs
  PreOp p f -> (case p of
    QuantF q as -> PreOp (QuantF (case q of
      AllValuesFrom -> SomeValuesFrom
      SomeValuesFrom -> AllValuesFrom) as)
    X -> PreOp X
    F -> PreOp G
    G -> PreOp F
    NotF -> id) $ negFoltl f
  BinOp f1 p f2 -> case p of
    Until -> release (negFoltl f1) $ negFoltl f2
    Impl -> JoinedF IntersectionOf [negFoltl f1, negFoltl f2]

-- <http://en.wikipedia.org/wiki/Linear_temporal_logic>
weakUntil :: Foltl -> Foltl -> Foltl
weakUntil f1 f2 = JoinedF UnionOf [BinOp f1 Until f2, PreOp G f1]

release :: Foltl -> Foltl -> Foltl
release f1 f2 = weakUntil f2 $ JoinedF IntersectionOf [f1, f2]

data Header = Header String [String]
  deriving (Show, Eq, Ord)

data Monitor = Monitor Header (Maybe String) Foltl
  deriving (Show, Eq, Ord)

type ABoxLit = (Bool, ABox)

type ABoxDeletes = [Either ABoxLit [String]]

type ABoxs = [ABox]

type ABoxAnds = [ABoxLit]

data CondEffect = CondEffect ABox ABoxDeletes
  deriving (Show, Eq, Ord)

data Exec = Exec String String [String]
  deriving (Show, Eq, Ord)

data Action = Action Header ABoxs ABoxDeletes [CondEffect] (Maybe Exec)
  deriving (Show, Eq, Ord)

data IndEffect = IndEffect String ABoxs ABoxDeletes ABoxs
  deriving (Show, Eq, Ord)

data Process = Process Header Proc
  deriving (Show, Eq, Ord)

data Proc
  = While ABoxAnds Proc
  | Star Proc
  | Quest ABox
  | IfElse ABoxAnds Proc Proc
  | Switch [(Maybe ABoxAnds, Proc)]
  | Forall ABoxAnds Proc
  | Init Foltl
  | CallP String [String]
  | BinP BinP [Proc]
  deriving (Show, Eq, Ord)

data BinP = Semi | Pipe | SeqPlus deriving (Show, Eq, Ord)

data Ship
  = ShipP Process
  | ShipA Action
  | ShipI IndEffect
  deriving (Show, Eq, Ord)

isPrimFoltl :: Foltl -> Bool
isPrimFoltl ftl = case ftl of
  ABoxass _ -> True
  Call {} -> True
  PreOp _ f -> isPrimFoltl f
  _ -> False

lastNotPrim :: [Foltl] -> Bool
lastNotPrim l = not (null l) && not (isPrimFoltl $ last l)

ppJFoltl :: Bool -> JunctionType -> Foltl -> Doc
ppJFoltl first j f = case f of
    JoinedF t l -> (if t /= j && t == UnionOf
      || first && lastNotPrim l then parens else id) $ ppFoltl f
    _ -> ppBFoltl first f

ppBFoltl :: Bool -> Foltl -> Doc
ppBFoltl first f = case f of
    BinOp {} -> parens
    JoinedF _ l | first && lastNotPrim l
      -> parens
    PreOp {} | first -> parens
    _ -> id
  $ ppFoltl f

ppFoltl :: Foltl -> Doc
ppFoltl ft = case ft of
  ABoxass a -> ppABox a
  Call b s ps -> (if b then keyword "run" else empty)
    <+> text s <> if null ps then empty else ppParams ps
  JoinedF t l -> case reverse l of
    [] -> empty
    f : r -> fsep . prepPunctuate (text $ case t of
      UnionOf -> "or "
      IntersectionOf -> "and ")
      . reverse $ ppJFoltl False t f : map (ppJFoltl True t) r
  PreOp p f -> let
    d1 = ppPreOp p
    d2 = ppFoltl f
    d3 = d1 <+> d2
    in case p of
    QuantF {} -> fsep [d1, bullet <+> d2]
    NotF -> case f of
      PreOp {} -> d3
      _ -> if isPrimFoltl f then d3 else d1 <> parens d2
    _ -> d3
  BinOp f1 o f2 -> fsep
    [ ppBFoltl True f1
    , case o of
              Until -> keyword "U"
              Impl -> implies
    , ppBFoltl False f2 ]

ppPreOp :: PreOp -> Doc
ppPreOp o = case o of
  QuantF q as -> keyword (showQuant q) <+> sepByCommas (map ppABox as)
  NotF -> keyword "not"
  _ -> keyword (show o)

ppHeader :: Header -> Doc
ppHeader (Header name ps) = text name <>
       (if null ps then empty else ppParams ps)
    <+> equals

ppMonitor :: Monitor -> Doc
ppMonitor (Monitor h mc ft) = fsep
  $ (keyword "monitor" <+> ppHeader h)
  : case mc of
      Nothing -> []
      Just c -> [doubleQuotes . text $ filter (/= '"') c]
  ++ [ppFoltl ft]

ppMon :: [Monitor] -> Doc
ppMon = vsep . map ppMonitor

ppABoxLit :: ABoxLit -> Doc
ppABoxLit (b, a) = (if b then empty else keyword "not") <+> ppABox a

ppABoxDelete :: Either ABoxLit [String] -> Doc
ppABoxDelete e = case e of
  Left a -> ppABoxLit a
  Right l -> keyword "delete" <> ppParams l

ppABoxDeletes :: ABoxDeletes -> Doc
ppABoxDeletes = sepByCommas . map ppABoxDelete

ppABoxs :: ABoxs -> Doc
ppABoxs = sepByCommas . map ppABox

ppABoxAnds :: ABoxAnds -> Doc
ppABoxAnds = fsep . prepPunctuate (text "and ") . map ppABoxLit

ppCondEffect :: CondEffect -> Doc
ppCondEffect (CondEffect a as) =
  fsep [keyword "if" <+> parens (ppABox a), ppABoxDeletes as]

eqKey :: String -> Doc
eqKey s = keyword s <+> equals

ppParams :: [String] -> Doc
ppParams = parens . sepByCommas . map text

ppExec :: Exec -> [Doc]
ppExec (Exec s1 s2 ps) =
  [eqKey "exec" <+> text s1 <> dot <> text s2 <> ppParams ps]

ppAction :: Action -> Doc
ppAction (Action h pre eff cs me) = fsep
  [ keyword "action" <+> ppHeader h
  , braces $ vcat
    $ [ if null pre then empty else eqKey "pre" <+> ppABoxs pre
      , if null eff then empty else eqKey "effect" <+> ppABoxDeletes eff]
    ++ map ppCondEffect cs
    ++ maybe [] ppExec me]

ppIndEffect :: IndEffect -> Doc
ppIndEffect (IndEffect n is cs ds) = fsep
  [ keyword "indirect" <+> keyword "effect" <+> ppHeader (Header n [])
  , braces $ vcat
    [ eqKey "init" <+> ppABoxs is
    , eqKey "causes" <+> ppABoxDeletes cs
    , eqKey "cond" <+> ppABoxs ds]]

ppProcess :: Process -> Doc
ppProcess (Process h p) = fsep
  [ keyword "function" <+> ppHeader h, braces $ ppProc p]

ppProc :: Proc -> Doc
ppProc pr = case pr of
  While as p -> fsep
    [keyword "while" <+> parens (ppABoxAnds as), ppProc p]
  Star p -> (if isPrim p then id else parens) (ppProc p) <> text "*"
  Quest a -> ppABox a <> text "?"
  IfElse as p1 p2 -> fsep
    [ keyword "if" <+> parens (ppABoxAnds as), ppProc p1
    , keyword "else" <+> ppProc p2]
  Switch cs -> keyword "switch" <+>
    vcat (map (\ (m, p) -> fsep
      [keyword "case" <+> maybe (text "_") ppABoxAnds m, implies <+> ppProc p])
          cs)
  Forall as p -> fsep
    [keyword "forall" <+> ppABoxAnds as, implies <+> ppProc p]
  Init f -> keyword "init" <+> ppFoltl f
  CallP n ps -> text n <> ppParams ps
  BinP o ps -> case reverse ps of
    [] -> empty
    f : r -> fsep . prepPunctuate (ppBinP o)
      . reverse $ ppBinProc False o f : map (ppBinProc True o) r

isPrim :: Proc -> Bool
isPrim p = case p of
  Star _ -> True
  Quest _ -> True
  CallP {} -> True
  Init {} -> True
  _ -> False

lastIsPrim :: Proc -> Bool
lastIsPrim pr = case pr of
  While _ p -> lastIsPrim p
  IfElse _ _ p -> lastIsPrim p
  Forall _ p -> lastIsPrim p
  Switch l -> null l || lastIsPrim (snd $ last l)
  _ -> isPrim pr

ppBinProc :: Bool -> BinP -> Proc -> Doc
ppBinProc first b p = case p of
      BinP o ps | o <= b -> if first && not (null ps || isPrim (last ps))
                            then parens else id
      _ | first -> if isPrim p then id else parens
      _ | lastIsPrim p -> id
      _ -> parens
  $ ppProc p

ppBinP :: BinP -> Doc
ppBinP b = text $ case b of
  Semi -> "; "
  Pipe -> "| "
  SeqPlus -> "+> "

ppShip :: Ship -> Doc
ppShip s = case s of
  ShipP p -> ppProcess p
  ShipA a -> ppAction a
  ShipI i -> ppIndEffect i

ppShips :: [Ship] -> Doc
ppShips = vsep . map ppShip

aboxVar :: CharParser st [ABox]
aboxVar = liftM2 (\ ns c -> map (`AConcept` c) ns)
  (sepBy nominal commaP)
  (colonP >> concept)

aboxVars :: CharParser st [ABox]
aboxVars = flat $ sepBy aboxVar commaP

foltl, primFoltl, preFoltl, quantFoltl, andFoltl, orFoltl :: CharParser st Foltl

primFoltl = fmap ABoxass (try abox)
  <|> fmap (PreOp NotF) (skipKey "not" >> quantFoltl)
  <|> parent foltl

preFoltl = liftM2 PreOp
   (choice $ map (\ p -> skipKey (show p) >> return p) [X, F, G])
   foltl
   <|> primFoltl

quantFoltl = do
    q <- quant << skip
    as <- aboxVars
    bulletP
    f <- foltl
    return $ PreOp (QuantF q as) f
  <|> preFoltl
  <|> (option False (skipKey "run" >> return True) >>= callFoltl)

andFoltl = binP (JoinedF IntersectionOf) "and" quantFoltl
orFoltl = binP (JoinedF UnionOf) "or" andFoltl

impliesP :: GenParser Char st ()
impliesP = tryString "=>" >> skip

foltl = do
  f <- orFoltl
  option f $ liftM2 (BinOp f)
    ((skipKey "U" >> return Until) <|> (impliesP >> return Impl))
    foltl

optNoms :: GenParser Char st [String]
optNoms = optionL . parent $ sepBy nominal commaP

callFoltl :: Bool -> GenParser Char st Foltl
callFoltl b = liftM2 (Call b)
    (reserved (map show [X, F, G]
                   ++ ["run", "monitor", "and", "or", "U"]) nominal)
    optNoms

header :: CharParser st Header
header = liftM2 Header nominal optNoms << equalP

monitor :: CharParser st Monitor
monitor = do
  skipKey "monitor"
  h <- header
  mc <- optionMaybe $ char '"' >> many (noneOf "\n\"") << skipChar '"'
  f <- foltl
  return $ Monitor h mc f

mon :: CharParser st [Monitor]
mon = many1 monitor

aBoxLit :: CharParser st ABoxLit
aBoxLit = pair (option True $ skipKey "not" >> return False) abox

aBoxDelete :: CharParser st (Either ABoxLit [String])
aBoxDelete = fmap Right (skipKey "delete" >> parent (sepBy nominal commaP))
  <|> fmap Left aBoxLit

aBoxDeletes :: CharParser st ABoxDeletes
aBoxDeletes = sepBy aBoxDelete commaP

aBoxs :: CharParser st ABoxs
aBoxs = sepBy abox commaP

aBoxAnds :: CharParser st ABoxAnds
aBoxAnds = sepBy1 aBoxLit (skipKey "and")

condEffect :: CharParser st CondEffect
condEffect = skipKey "fi" >> liftM2 CondEffect (parent abox) aBoxDeletes

skipEqKey :: String -> CharParser st ()
skipEqKey s = skipKey s >> equalP

exec :: CharParser st Exec
exec = do
  let name = many1 myLetter
  skipEqKey "exec"
  s1 <- name << char '.'
  s2 <- name << skip
  ps <- optNoms
  return $ Exec s1 s2 ps

action :: CharParser st Action
action = do
  h <- skipKey "action" >> header
  braced $ do
    as <- optionL $ skipEqKey "pre" >> aBoxs
    ds <- optionL $ skipEqKey "effect" >> aBoxDeletes
    cs <- many condEffect
    me <- optionMaybe exec
    return $ Action h as ds cs me

indEffect :: CharParser st IndEffect
indEffect = do
  s <- skipKey "indirect" >> skipKey "effect" >> nominal
  equalP
  braced $ do
    as <- skipEqKey "init" >> aBoxs
    cs <- skipEqKey "causes" >> aBoxDeletes
    ds <- skipEqKey "cond" >> aBoxs
    return $ IndEffect s as cs ds

process :: CharParser st Process
process = skipKey "function" >> liftM2 Process header proc

primProc, starProc, preProc, semiProc, pipeProc, proc :: CharParser st Proc

primProc = braced proc
  <|> parent proc
  <|> fmap Init (try $ skipKey "init" >> foltl)
  <|> fmap Quest (try $ abox << skipChar '?')
  <|> liftM2 CallP
      (reserved ["while", "forall", "if", "switch"] nominal)
      optNoms

starProc = do
  p <- primProc
  ls <- many $ skipChar '*'
  return $ if null ls then p else Star p

preProc = liftM2 While (skipKey "while" >> parent aBoxAnds) proc
  <|> liftM3 IfElse (skipKey "if" >> parent aBoxAnds) proc
          (skipKey "else" >> proc)
  <|> liftM2 Forall (skipKey "forall" >> aBoxAnds) (impliesP >> proc)
  <|> fmap Switch (skipKey "switch" >>
         many (skipKey "case" >> pair
               (fmap Just aBoxAnds <|> (skipChar '_' >> return Nothing))
               (impliesP >> proc)))
  <|> starProc

semiProc = binC (BinP Semi) ';' preProc
pipeProc = binC (BinP Pipe) '|' semiProc
proc = binPP (BinP SeqPlus) ((tryString "+>" >> skip) <|> skipChar '+') pipeProc

ship :: CharParser st Ship
ship = fmap ShipP process <|> fmap ShipA action <|> fmap ShipI indEffect

ships :: CharParser st [Ship]
ships = many ship

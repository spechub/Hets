{- |
Module      :  ./ExtModal/Parse_AS.hs
Description :  Parser for extended modal logic
Copyright   :  DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module ExtModal.Parse_AS (ext_modal_reserved_words) where

import Text.ParserCombinators.Parsec

import Common.AS_Annotation
import Common.Id
import Common.Parsec
import Common.Token
import Common.Lexer
import Common.AnnoState
import Common.Keywords

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.OpItem
import CASL.Parse_AS_Basic

import ExtModal.AS_ExtModal
import ExtModal.Keywords

import Data.Maybe

-- | List of reserved words
ext_modal_reserved_words :: [String]
ext_modal_reserved_words = map show [Intersection, Union] ++
  [ untilS
  , sinceS
  , allPathsS
  , somePathsS
  , nextS
  , yesterdayS
  , generallyS
  , eventuallyS
  , atS
  , quMark
  , hereS
  , timeS
  , nominalS
  , nominalS ++ sS
  , hithertoS
  , previouslyS
  , muS
  , nuS
  , diamondS
  , orElseS
  , oB
  , cB
  , termS
  , rigidS
  , flexibleS
  , modalityS
  , modalitiesS ]

boxParser :: AParser st (MODALITY, BoxOp, Range)
boxParser = do
    let asESep = pToken . tryString
    open <- oBracketT <|> asESep oB
    let isBox = tokStr open == "["
    modal <- parseModality
    close <- if isBox then cBracketT else asESep cB
    return (modal, if isBox then Box else EBox, toRange open [] close)

diamondParser :: AParser st (MODALITY, BoxOp, Range)
diamondParser = do
    open <- asKey lessS
    modal <- parseModality
    close <- asKey greaterS
    return (modal, Diamond, toRange open [] close)
  <|> do
    d <- asKey diamondS
    let p = tokPos d
    return (SimpleMod $ Token emptyS p, Diamond, p)

rekPrimParser :: AParser st (FORMULA EM_FORMULA)
rekPrimParser = genPrimFormula modalPrimFormulaParser ext_modal_reserved_words

infixTok :: AParser st (Token, Bool)
infixTok = pair (asKey untilS) (return True)
    <|> pair (asKey sinceS) (return False)

-- | Modal infix formula parser
modalFormulaParser :: AParser st EM_FORMULA
modalFormulaParser = do
    p1 <- modalPrimFormulaParser
    option p1 $ do
      (t, b) <- infixTok
      f2 <- rekPrimParser
      return $ UntilSince b (ExtFORMULA p1) f2 $ tokPos t
  <|> do
    (f1, (t, b)) <- try $ pair rekPrimParser infixTok
    f2 <- rekPrimParser
    return $ UntilSince b f1 f2 $ tokPos t

prefixModifier :: AParser st (FormPrefix, Range)
prefixModifier = let mkF f r = return (f, tokPos r) in
      (asKey allPathsS >>= mkF (PathQuantification True))
  <|> (asKey somePathsS >>= mkF (PathQuantification False))
  <|> (asKey nextS >>= mkF (NextY True))
  <|> (asKey yesterdayS >>= mkF (NextY False))
  <|> (asKey generallyS >>= mkF (StateQuantification True True))
  <|> (asKey eventuallyS >>= mkF (StateQuantification True False))
  <|> (asKey hithertoS >>= mkF (StateQuantification False True))
  <|> (asKey previouslyS >>= mkF (StateQuantification False False))
  <|> do
    mnb <- (asKey muS >> return True)
      <|> (asKey nuS >> return False)
    z <- varId ext_modal_reserved_words
    dotT
    mkF (FixedPoint mnb z) z
  <|> do
    ahb <- (asKey atS >> return True)
      <|> (asKey hereS >> return False)
    nom <- simpleId
    mkF (Hybrid ahb nom) nom
  <|> do
    (modal, b, r) <- boxParser <|> diamondParser
    (lgb, val) <- option (True, 1) $ do
       lgb <- option False $ (asKey lessEq >> return False)
         <|> (asKey greaterEq >> return True)
       number <- getNumber << skipSmart
       return (lgb, value 10 number)
    return (BoxOrDiamond b modal lgb val, r)

-- | Modal formula parser
modalPrimFormulaParser :: AParser st EM_FORMULA
modalPrimFormulaParser = fmap ModForm modDefnParser <|> do
    (f, r) <- prefixModifier
    em_formula <- rekPrimParser
    return $ PrefixForm f em_formula r

-- | Term modality parser
parsePrimModality :: AParser st MODALITY
parsePrimModality =
  let fp = formula $ greaterS : ext_modal_reserved_words in do
          f <- try fp
          case f of
            Mixfix_formula t -> return $ TermMod t
            _ -> asSeparator quMark >> return (Guard f)
        <|> (oParenT >> parseModality << cParenT)
        <|> fmap Guard fp -- fail if something was consumed in the first try
        <|> fmap (SimpleMod . Token emptyS . Range . (: [])) getPos

parseTransClosModality :: AParser st MODALITY
parseTransClosModality = do
  t <- parsePrimModality
  mt <- many $ asKey tmTransClosS
  return $ if null mt then t else TransClos t

parseCompModality :: AParser st MODALITY
parseCompModality = parseBinModality Composition parseTransClosModality

parseInterModality :: AParser st MODALITY
parseInterModality = parseBinModality Intersection parseCompModality

parseUnionModality :: AParser st MODALITY
parseUnionModality = parseBinModality Union parseInterModality

parseBinModality :: ModOp -> AParser st MODALITY -> AParser st MODALITY
parseBinModality c p = do
  t1 <- p
  option t1 $ do
    asKey $ show c
    t2 <- parseBinModality c p
    return $ ModOp c t1 t2

-- | orElse binds weakest
parseModality :: AParser st MODALITY
parseModality = parseBinModality OrElse parseUnionModality

instance TermParser EM_FORMULA where
    termParser = aToTermParser modalFormulaParser

-- Signature parser

rigor :: AParser st Bool
rigor = (asKey rigidS >> return True)
        <|> (asKey flexibleS >> return False)

sigItemParser :: AParser st EM_SIG_ITEM
sigItemParser = do
  rig <- rigor
  itemList ext_modal_reserved_words opS opItem (Rigid_op_items rig)
    <|> itemList ext_modal_reserved_words predS predItem (Rigid_pred_items rig)

instance AParsable EM_SIG_ITEM where
        aparser = sigItemParser

-- Basic item parser

mKey :: AParser st Token
mKey = asKey modalityS <|> asKey modalitiesS

nKey :: AParser st Token
nKey = asKey nominalS <|> asKey (nominalS ++ sS)

modDefnParser :: AParser st ModDefn
modDefnParser = do
    mtime <- optionMaybe $ asKey timeS
    mterm <- optionMaybe $ asKey termS
    k <- mKey
    (ids, ks) <- separatedBy
      (annoParser $ sortId ext_modal_reserved_words) anSemiOrComma
    parseAxioms (ModDefn (isJust mtime) (isJust mterm) ids)
                           $ catRange $ k : ks

basicItemParser :: AParser st EM_BASIC_ITEM
basicItemParser = fmap ModItem modDefnParser <|> do
    k <- nKey
    (annoId, ks) <- separatedBy (annoParser simpleId) anSemiOrComma
    return $ Nominal_decl annoId $ catRange $ k : ks

parseAxioms :: ([Annoted FrameForm] -> Range -> a) -> Range -> AParser st a
parseAxioms mki pos =
         do o <- oBraceT
            someAxioms <- annosParser parseFrames
            c <- cBraceT
            return $ mki someAxioms
              $ pos `appRange` toRange o [] c
         <|> return (mki [] pos)

parseFrames :: AParser st FrameForm
parseFrames = do
    v <- pluralKeyword varS
    (vs, ps) <- varItems ext_modal_reserved_words
    return $ FrameForm vs [] $ catRange $ v : ps
  <|> do
    f <- forallT
    (vs, ps) <- varDecls ext_modal_reserved_words
    a <- annos
    emDotFormulae a vs $ catRange $ f : ps
  <|> emDotFormulae [] [] nullRange

axiomsToFrames :: [Annotation] -> [VAR_DECL] -> Range
  -> BASIC_ITEMS () () EM_FORMULA -> FrameForm
axiomsToFrames a vs posl ais = case ais of
  Axiom_items (Annoted ft qs as rs : fs) ds ->
         let aft = Annoted ft qs (a ++ as) rs
         in FrameForm vs (aft : fs) (posl `appRange` ds)
  _ -> error "axiomsToFrames"

emDotFormulae :: [Annotation] -> [VAR_DECL] -> Range -> AParser st FrameForm
emDotFormulae a v p = fmap (axiomsToFrames a v p)
  $ dotFormulae False ext_modal_reserved_words

instance AParsable EM_BASIC_ITEM where
        aparser = basicItemParser

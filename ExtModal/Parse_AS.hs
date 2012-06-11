{- |
Module      :  $Header$
Description :  Parser for extended modal logic
Copyright   :  DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module ExtModal.Parse_AS (ext_modal_reserved_words) where

import Text.ParserCombinators.Parsec

import Common.Id
import Common.Parsec
import Common.Token
import Common.Lexer
import Common.AnnoState
import Common.Keywords

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.OpItem

import ExtModal.AS_ExtModal
import ExtModal.Keywords

import Data.Maybe
import Data.List

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
  , termS
  , rigidS
  , flexibleS
  , modalityS
  , modalitiesS ]

boxParser :: AParser st (MODALITY, Bool, Range)
boxParser = do
    open <- oBracketT
    modal <- parseModality
    close <- cBracketT
    return (modal, True, toRange open [] close)

diamondParser :: AParser st (MODALITY, Bool, Range)
diamondParser = do
    open <- asKey lessS
    modal <- parseModality
    close <- asKey greaterS
    return (modal, False, toRange open [] close)
  <|> do
    d <- asKey diamondS
    let p = tokPos d
    return (SimpleMod $ Token emptyS p, False, p)

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

prefixModifier :: AParser st (FORMULA EM_FORMULA -> EM_FORMULA)
prefixModifier = let mkF f r = return $ flip f $ tokPos r in
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

-- | Modal formula parser
modalPrimFormulaParser :: AParser st EM_FORMULA
modalPrimFormulaParser = fmap ModForm modDefnParser <|> do
    (modal, b, r) <- boxParser <|> diamondParser
    (lgb, val) <- option (False, 1) $ do
       lgb <- (asKey lessEq >> return True)
         <|> (asKey greaterEq >> return False)
       number <- getNumber << skipSmart
       return (lgb, value 10 number)
    em_formula <- rekPrimParser
    return $ BoxOrDiamond b modal lgb val em_formula r
  <|> do
    f <- prefixModifier
    em_formula <- rekPrimParser
    return $ f em_formula

-- | Term modality parser
parsePrimModality :: AParser st MODALITY
parsePrimModality = do
           oParenT
           t <- parseModality
           cParenT
           return t
        <|> do
          f <- formula $ greaterS : ext_modal_reserved_words
          case f of
            Mixfix_formula t -> return $ TermMod t
            _ -> asSeparator quMark >> return (Guard f)
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

parseBinModality :: ModOp -> AParser st MODALITY -> AParser st MODALITY
parseBinModality c p = do
  t1 <- p
  option t1 $ do
    asKey $ show c
    t2 <- parseBinModality c p
    return $ ModOp c t1 t2

parseModality :: AParser st MODALITY
parseModality = parseBinModality Union parseInterModality

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

parseAxioms :: ([AnEModForm] -> Range -> a) -> Range -> AParser st a
parseAxioms mki pos =
         do o <- oBraceT
            (someAxioms, qs) <- auxItemList
              (delete diamondS ext_modal_reserved_words) []
                      (formula ext_modal_reserved_words) (,)
            c <- cBraceT
            return $ mki someAxioms
              $ pos `appRange` qs `appRange` toRange o [] c
         <|> return (mki [] pos)

instance AParsable EM_BASIC_ITEM where
        aparser = basicItemParser

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
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.OpItem

import ExtModal.AS_ExtModal
import ExtModal.Keywords

import Data.Maybe

-- | List of reserved words
ext_modal_reserved_words :: [String]
ext_modal_reserved_words =
  [ untilS
  , sinceS
  , allPathsS
  , somePathsS
  , nextS
  , yesterdayS
  , generallyS
  , eventuallyS
  , atS
  , hereS
  , timeS
  , nominalS
  , nominalsS
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
    return (Simple_modality $ Token emptyS p, False, p)

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
    mkF (Hybrid ahb $ Nominal nom) nom

-- | Modal formula parser
modalPrimFormulaParser :: AParser st EM_FORMULA
modalPrimFormulaParser = do
    (modal, b, r) <- boxParser <|> diamondParser
    (lgb, val) <- option (True, 1) $ do
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
           mf <- optionMaybe $ formula $ greaterS : ext_modal_reserved_words
           case mf of
             Nothing ->
               fmap (Simple_modality . Token emptyS . Range . (: [])) getPos
             Just f -> do
                asSeparator tmGuardS
                return $ Guard f
              <|> case f of
                Mixfix_formula (Mixfix_token t) | isSimpleToken t ->
                  return $ Simple_modality t
                _ -> pzero

parseTransClosModality :: AParser st MODALITY
parseTransClosModality = do
  t <- parsePrimModality
  mt <- many $ asKey tmTransClosS
  return $ if null mt then t else TransitiveClosure t

parseCompModality :: AParser st MODALITY
parseCompModality = do
  t1 <- parseTransClosModality
  option t1 $ do
    asKey tmCompositionS
    t2 <- parseCompModality
    return $ Composition t1 t2

parseModality :: AParser st MODALITY
parseModality = do
  t1 <- parseCompModality
  option t1 $ do
    asKey tmUnionS
    t2 <- parseModality
    return $ Union t1 t2

instance TermParser EM_FORMULA where
    termParser = aToTermParser modalFormulaParser

-- Signature parser

rigor :: AParser st RIGOR
rigor = (asKey rigidS >> return Rigid)
        <|> (asKey flexibleS >> return Flexible)

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
nKey = asKey nominalS <|> asKey nominalsS

basicItemParser :: AParser st EM_BASIC_ITEM
basicItemParser =
        do mt <- optionMaybe $ asKey timeS
           k <- mKey
           (annoId, ks) <- separatedBy (annoParser simpleId) anSemiOrComma
           parseAxioms (isJust mt) annoId $ catRange $ k : ks
        <|>
        do k <- nKey
           (annoId, ks) <- separatedBy (annoParser simpleId) anSemiOrComma
           return $ Nominal_decl annoId $ catRange $ k : ks

parseAxioms :: Bool -> [Annoted SIMPLE_ID] -> Range -> AParser st EM_BASIC_ITEM
parseAxioms b annoId pos =
         do o <- oBraceT
            (someAxioms, qs) <- annoParser (formula ext_modal_reserved_words)
                  `separatedBy` anSemi
            c <- cBraceT
            return (Simple_mod_decl b annoId someAxioms
                   $ pos `appRange` toRange o qs c)
         <|> return (Simple_mod_decl b annoId [] pos)

instance AParsable EM_BASIC_ITEM where
        aparser = basicItemParser

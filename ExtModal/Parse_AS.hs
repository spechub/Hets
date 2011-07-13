{- |
Module      :  $Header$
Description :  Parser for extended modal logic
Copyright   :  DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module ExtModal.Parse_AS where

import Text.ParserCombinators.Parsec

import Common.Id
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
  , generallyS
  , eventuallyS
  , generallyS
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

-- | Modal formula parser
modalFormulaParser :: AParser st EM_FORMULA
-- common beginnings must be factored out
modalFormulaParser =
        -- box, <=
        do open <- oBracketT
           modal <- parseModality
           close <- cBracketT
           asKey lessEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           return (BoxOrDiamond True modal True (value 10 number) em_formula
                  $ toRange open [] close)
        <|>
        -- box, >=
        do open <- oBracketT
           modal <- parseModality
           close <- cBracketT
           asKey greaterEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           return (BoxOrDiamond True modal False (value 10 number) em_formula
                  $ toRange open [] close)
        <|>
        -- diamond, <=
        do open <- asKey lessS
           modal <- parseModality
           close <- asKey greaterS
           asKey lessEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           return (BoxOrDiamond False modal True (value 10 number) em_formula
                  $ toRange open [] close)
        <|>
        -- diamond, >=
        do open <- asKey lessS
           modal <- parseModality
           close <- asKey greaterS
           asKey greaterEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           return (BoxOrDiamond False modal False (value 10 number) em_formula
                  $ toRange open [] close)
        <|>
        -- empty diamond, <=
        do diam <- asKey diamondS
           asKey lessEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos diam
           return (BoxOrDiamond False (Simple_modality $ Token emptyS pos)
                   True (value 10 number) em_formula pos)
        <|>
        -- empty diamond, >=
        do diam <- asKey diamondS
           asKey greaterEq
           number <- getNumber
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos diam
           return (BoxOrDiamond False (Simple_modality $ Token emptyS pos)
                   False (value 10 number) em_formula pos)
        <|>
        -- Until, U
        do formula1 <- primCASLFormula ext_modal_reserved_words
           unt <- asKey untilS
           formula2 <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos unt
           return (UntilSince True formula1 formula2 pos)
        <|>
        -- Since, S
        do formula1 <- primCASLFormula ext_modal_reserved_words
           snc <- asKey sinceS
           formula2 <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos snc
           return (UntilSince False formula1 formula2 pos)
        <|>
        -- All paths, A
        do ap <- asKey allPathsS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos ap
           return (PathQuantification True em_formula pos)
        <|>
        -- Some paths, E
        do sp <- asKey somePathsS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos sp
           return (PathQuantification False em_formula pos)
        <|>
        -- Next, X
        do nxt <- asKey nextS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos nxt
           return (NextY True em_formula pos)
        <|>
        -- Yesterday, Y
        do ysd <- asKey yesterdayS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos ysd
           return (NextY False em_formula pos)
        <|>
        -- Generally, G
        do grl <- asKey generallyS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos grl
           return (StateQuantification True True em_formula pos)
        <|>
        -- Eventually, F
        do evt <- asKey eventuallyS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos evt
           return (StateQuantification True False em_formula pos)
        <|>
        -- Hitherto, H
        do hth <- asKey hithertoS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos hth
           return (StateQuantification False True em_formula pos)
        <|>
        -- Previously, P
        do prv <- asKey previouslyS
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos prv
           return (StateQuantification False False em_formula pos)
        <|>
        -- parse Mu
        do mu <- asKey muS
           z <- varId ext_modal_reserved_words
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos mu
           return (FixedPoint True z em_formula pos)
        <|>
        -- parse Nu
        do nu <- asKey nuS
           z <- varId ext_modal_reserved_words
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos nu
           return (FixedPoint False z em_formula pos)
        <|>
        -- @
        do at <- asKey atS
           nom <- simpleId
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos at
           return (Hybrid True (Nominal nom) em_formula pos)
        <|>
        -- Here
        do her <- asKey hereS
           nom <- simpleId
           em_formula <- primCASLFormula ext_modal_reserved_words
           let pos = tokPos her
           return (Hybrid False (Nominal nom) em_formula pos)

-- | Term modality parser
parsePrimModality :: AParser st MODALITY
parsePrimModality = do
           asKey tmOParanthS
           t <- parseModality
           asKey tmCParanthS
           return t
        <|> do
           mf <- optionMaybe $ primCASLFormula ext_modal_reserved_words
           case mf of
             Nothing -> return $ Simple_modality $ mkSimpleId emptyS
             Just f -> case f of
               Mixfix_formula (Mixfix_token t) | isSimpleToken t ->
                 return $ Simple_modality t
               _ -> do
                 asKey tmGuardS
                 return $ Guard f

parseTransClosModality :: AParser st MODALITY
parseTransClosModality = do
  t <- parsePrimModality
  mt <- optionMaybe $ asKey tmTransClosS
  return $ if isJust mt then TransitiveClosure t else t

parseCompModality :: AParser st MODALITY
parseCompModality = do
  t1 <- parsePrimModality
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
        do k <- mKey
           (annoId, ks) <- separatedBy (annoParser simpleId) anComma
           parseAxioms False annoId ( catRange $ k : ks )
        <|>
        do asKey timeS
           k <- mKey
           (annoId, ks) <- separatedBy (annoParser simpleId) anComma
           parseAxioms True annoId ( catRange $ k : ks )
        <|>
        do k <- nKey
           (annoId, ks) <- separatedBy (annoParser simpleId) anComma
           let pos = catRange $ k : ks
           return (Nominal_decl annoId pos)

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

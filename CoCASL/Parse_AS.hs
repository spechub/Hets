{- |
Module      :  $Header$
Description :  Parser for CoCASL
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for CoCASL
-}

module CoCASL.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import CoCASL.AS_CoCASL
import Text.ParserCombinators.Parsec
import CASL.Formula
import CASL.Parse_AS_Basic (sigItems)
import CASL.AS_Basic_CASL

cocasl_reserved_words :: [String]
cocasl_reserved_words = [diamondS]

cocaslFormula :: AParser st C_FORMULA
cocaslFormula = do
    o <- oBracketT
    m <- modality []
    c <- cBracketT
    f <- formula cocasl_reserved_words
    return (BoxOrDiamond True m f $ toRange o [] c)
  <|> do
    o <- asKey lessS
    m <- modality [greaterS] -- do not consume matching ">"!
    c <- asKey greaterS
    f <- formula cocasl_reserved_words
    return (BoxOrDiamond False m f $ toRange o [] c)

modality :: [String] -> AParser st MODALITY
modality ks = do
    t <- term (prodS : ks ++ cocasl_reserved_words)
            -- put the term in parens if you need to use "*"
    option () (asKey prodS >> return ())
       -- presence of "*" is not stored yet!
    return $ case t of
      Mixfix_token tok -> Simple_mod tok
      _ -> Term_mod t

instance TermParser C_FORMULA where
  termParser = aToTermParser cocaslFormula

cBasic :: AParser st C_BASIC_ITEM
cBasic = do
    f <- asKey cofreeS
    ti <- coSigItems
    return (codatatypeToCofreetype ti (tokPos f))
  <|> do
    g <- asKey cogeneratedS
    do t <- sigItems cocasl_reserved_words
       return (CoSort_gen [Annoted t nullRange [] []] $ tokPos g)
      <|> do
        o <- oBraceT
        is <- annosParser (sigItems cocasl_reserved_words)
        c <- cBraceT
        return (CoSort_gen is (toRange g [o] c))

coSigItems :: AParser st C_SIG_ITEM
coSigItems =
  itemList cocasl_reserved_words cotypeS codatatype CoDatatype_items

codatatype :: [String] -> AParser st CODATATYPE_DECL
codatatype ks = do
    s <- sortId ks
    addAnnos
    e <- asKey defnS
    addAnnos
    a <- getAnnos
    (Annoted v _ _ b : as, ps) <- acoAlternative ks `separatedBy` barT
    return $ CoDatatype_decl s (Annoted v nullRange a b : as)
      $ catRange $ e : ps

acoAlternative :: [String] -> AParser st (Annoted COALTERNATIVE)
acoAlternative ks = do
    a <- coalternative ks
    an <- annos
    return (Annoted a nullRange [] an)

coalternative :: [String] -> AParser st COALTERNATIVE
coalternative ks = do
    s <- pluralKeyword sortS
    (ts, cs) <- sortId ks `separatedBy` anComma
    return (CoSubsorts ts $ catRange $ s : cs)
  <|> do
    i <- consId ks
    cocomp ks (Just i)
  <|> cocomp ks Nothing

cocomp :: [String] -> Maybe OP_NAME -> AParser st COALTERNATIVE
cocomp ks i = do
    o <- oParenT
    (cs, ps) <- cocomponent ks `separatedBy` anSemi
    c <- cParenT
    let qs = toRange o ps c
    do q <- quMarkT
       return (Co_construct Partial i cs (qs `appRange` tokPos q))
      <|> return (Co_construct Total i cs qs)
  <|> return (Co_construct Total i [] nullRange)

cocomponent :: [String] -> AParser st COCOMPONENTS
cocomponent ks = do
    (is, cs) <- parseId ks `separatedBy` anComma
    c <- colonST
    t <- opType ks
    return $ CoSelect is t $ catRange $ cs ++ [c]

instance AParsable C_SIG_ITEM where
  aparser = coSigItems

instance AParsable C_BASIC_ITEM where
  aparser = cBasic

codatatypeToCofreetype :: C_SIG_ITEM -> Range -> C_BASIC_ITEM
codatatypeToCofreetype d pos = case d of
    CoDatatype_items ts ps -> CoFree_datatype ts (pos `appRange` ps)

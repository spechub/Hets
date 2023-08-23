{-# LANGUAGE RankNTypes #-}
{- |
Module      :  ./TopHybrid/Parse_AS.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  provisional
Portability :  portable


Description  :
Parser for an hybridized arbitrary logic
-}

module TopHybrid.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations (PrefixMap)
import Common.Token
import Data.Maybe
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec
import Logic.Logic
import TopHybrid.AS_TopHybrid
import Control.Monad (liftM)

-- the top parser; parses an entire specification
thBasic :: (String -> AnyLogic) -> AParser st Spc_Wrap
thBasic getLogic =
        do
        asKey "baselogic"
        logicName <- simpleId
        thSpec $ getLogic $ show logicName

basicSpec :: (Syntax lid basic_spec s si sim) =>
 lid -> Maybe (PrefixMap -> AParser st basic_spec)
basicSpec l = maybe (parse_basic_spec l) (Just . fst)
 (parserAndPrinter Nothing l)

{- Parses the specification after knowing
the underlying logic -}
thSpec :: AnyLogic -> AParser st Spc_Wrap
thSpec (Logic l) =
        do
        asKey "Basic_Spec"
        asKey "{"
        s <- callParser l basicSpec Map.empty
        asKey "}"
        i <- many itemParser
        fs <- sepBy (annoFormParser l s) anSemiOrComma
        return $ Spc_Wrap l (Bspec i s) fs

{- Calls the underlying logic parser, only if exists. Otherwise
will throw out an error -}
callParser :: (Show a) => a -> (a -> Maybe x) -> x
callParser l f =
 fromMaybe (error $ "Failed! No parser for logic " ++ show l) $ f l

-- Parses the declaration of nominals and modalities
itemParser :: AParser st TH_BASIC_ITEM
itemParser =
        do
        asKey "modalities"
        ms <- ids
        return $ Simple_mod_decl ms
        <|>
        do
        asKey "nominals"
        ns <- ids
        return $ Simple_nom_decl ns
        where ids = sepBy simpleId anSemiOrComma


-- Formula parser with annotations
annoFormParser :: (Logic l sub bs f s sm si mo sy rw pf) =>
                        l -> bs -> AParser st (Annoted Frm_Wrap)
annoFormParser l b = allAnnoParser $ formParser l b

-- Just parses the formula, and wraps it in Frm_Wrap
formParser :: (Logic l sub bs f s sm si mo sy rw pf) =>
                        l -> bs -> AParser st Frm_Wrap
formParser l bs = liftM (Frm_Wrap l) $ topParser l bs

-- Parser of hybridization of hybridization of sentences
formParser' :: Spc_Wrap -> AParser st Frm_Wrap
formParser' (Spc_Wrap l b _) = liftM (Frm_Wrap l) $ topParser l (und b)

{- Parser of sentences
The precendence order is left associative and when the priority
is defined is as follows : () > (not,@,[],<>) > /\ > \/ > (->,<->) -}
topParser :: (Logic l sub bs f s sm si mo sy rw pf) =>
                l -> bs -> AParser st (TH_FORMULA f)
topParser l bs = chainl1 fp1 impAndBiP
        where fp1 = chainl1 fp2 disjP
              fp2 = chainl1 (fParser l bs) conjP

{- BinaryOps parsers, the reason to separate them, is that so we can get a
precedence order -}
conjP :: AParser st (TH_FORMULA f -> TH_FORMULA f -> TH_FORMULA f)
conjP = asKey "/\\" >> return Conjunction

disjP :: AParser st (TH_FORMULA f -> TH_FORMULA f -> TH_FORMULA f)
disjP = asKey "\\/" >> return Disjunction

impAndBiP :: AParser st (TH_FORMULA f -> TH_FORMULA f -> TH_FORMULA f)
impAndBiP = (asKey "=>" >> return Implication) <|>
            (asKey "<=>" >> return BiImplication)
-- ------------

-- Parser of sentences without the binary operators
fParser :: (Logic l sub bs f s sm si mo sy rw pf) =>
                l -> bs -> AParser st (TH_FORMULA f)
fParser l bs =
        do
        asKey "("
        f <- topParser l bs
        asKey ")"
        return $ Par f
        <|>
        do
        asKey "not"
        f <- fParser l bs <|> topParser l bs
        return $ Neg f
        <|>
        do
        asKey "@"
        n <- simpleId
        f <- fParser l bs <|> topParser l bs
        return $ At n f
        <|>
        do
        asKey "!"
        n <- simpleId
        f <- fParser l bs
        return $ Uni n f
        <|>
        do
        asKey "?"
        n <- simpleId
        f <- fParser l bs
        return $ Exist n f
        <|>
        do
        asKey "["
        m <- simpleId
        asKey "]"
        f <- fParser l bs <|> topParser l bs
        return $ Box m f
        <|>
        try (do
        asKey "<"
        m <- simpleId
        asKey ">\""
        f <- fParser l bs <|> topParser l bs
        return $ Par $ Conjunction (Dia m f) (Box m f))
        <|>
        do
        asKey "<"
        m <- simpleId
        asKey ">"
        f <- fParser l bs <|> topParser l bs
        return $ Dia m f
        <|>
        do
        asKey "true"
        return TrueA
        <|>
        do
        asKey "false"
        return FalseA
        <|>
        do
        n <- simpleId
        return $ Here n
        <|>
        do
        asKey "{"
        f <- callParser l parse_basic_sen bs
        asKey "}"
        return $ UnderLogic f

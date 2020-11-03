{- |
Module      :  ./CASL/CompositionTable/ParseTable2.hs
Description :  parsing SparQ CompositionTables
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  fmossa@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parses CompositionTables in SparQ(Lisp)-Format using Parsec
 <http://www.cs.uu.nl/~daan/parsec.html>
-}

module CASL.CompositionTable.ParseTable2
  ( parseSparQTableFromFile
  , parseSparQTable
  , skip
  ) where

import Text.ParserCombinators.Parsec
import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.ModelTable
import CASL.CompositionTable.Keywords
import CASL.CompositionTable.ParseSparQ
import Common.Parsec
import Common.Utils

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Strict as Map
import Data.Char
import Data.List

parseSparQTableFromFile :: String -> IO (Either ParseError Table2)
parseSparQTableFromFile = parseFromFile (skip >> parseSparQTable << eof)

makeTable :: [Baserel] -> (BMap, Table2)
makeTable rs = (Map.fromList $ number rs, toTable2 $ Table
      (Table_Attrs "" (Baserel "") rs)
      (Compositiontable []) (Conversetable []) (Reflectiontable []) $ Models [])

parseSparQTable :: Parser Table2
parseSparQTable = inParens $ do
  calculusName <- parseCalculusName
  (i1, rs1) <- parseIdBaOths
  (m, Table2 _ _ ns bs _ _, ct, i2) <- if null rs1 then do
      ctOld <- parseConversetable
      (i2, rs2) <- parseIdBaOths
      let (m, t) = makeTable $ rs1 ++ rs2
      return (m, t, toConTables m ctOld, i1 ++ i2)
    else do
      let (m, t) = makeTable rs1
      ctNew <- parseConv m
      (i2, _) <- parseIdBaOths
      return (m, t, ctNew, i1 ++ i2)
  compt <- parseComTab m
  (i3, _) <- parseIdBaOths
  case i2 ++ i3 of
    [i] -> return $ Table2 calculusName (lkup i m) ns bs compt ct
    [] -> fail "missing identity relation"
    is -> fail $ "non-unique identity relation " ++ show is

parseComTab :: BMap -> Parser CmpTbl
parseComTab m = cKey compositionOperationS
  >> inParens (parseComptab m)

parseComptab :: BMap -> Parser CmpTbl
parseComptab = fmap
  (foldl' (\ t (r1, r2, rs) ->
     IntMap.insertWith IntMap.union r1
       (IntMap.insertWith IntSet.union r2 rs IntMap.empty) t)
  IntMap.empty)
  . many1 . parseComptabent

parseComptabent :: BMap -> Parser (Int, Int, IntSet.IntSet)
parseComptabent m = inParens $ do
  rel1 <- parseRel m
  rel2 <- parseRel m
  results <- parseComptabres m
  return (rel1, rel2, results)

parseComptabres :: BMap -> Parser IntSet.IntSet
parseComptabres m =
  inParens (fmap IntSet.fromList $ many $ parseRel m)
  <|> do
    result@(Baserel str) <- parseRelationId
    return $ if map toUpper str == "NIL" then IntSet.empty else
                 IntSet.singleton $ lkup result m

parseConv :: BMap -> Parser ConTables
parseConv m = let e = IntMap.empty in do
    e1 <- parseContab m inverseOperationS
    e2 <- parseContab m shortcutOperationS
    e3 <- parseContab m homingOperationS
    return (e, e1, e2, e3)
  <|> fmap (\ c -> (c, e, e, e)) (parseContab m converseOperationS)

parseContab :: BMap -> String -> Parser ConTable
parseContab m s = cKey s >> inParens (fmap
  (foldl' (\ t (i, r) -> IntMap.insertWith IntSet.union i r t) IntMap.empty)
  . many1 $ parseContabent m)

parseContabent :: BMap -> Parser (Int, IntSet.IntSet)
parseContabent m = inParens $
  pair (parseRel m) (parseRelIds m <|> inParens (parseRelIds m))

parseRelIds :: BMap -> Parser IntSet.IntSet
parseRelIds = fmap IntSet.fromList . many1 . parseRel

type BMap = Map.HashMap Baserel Int

parseRel :: BMap -> Parser Int
parseRel m = fmap (`lkup` m) parseRelationId
